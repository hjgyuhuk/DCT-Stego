package main

import (
	"errors"
	"flag"
	"fmt"
	"image"
	"image/color"
	"image/draw"
	"image/jpeg"
	"image/png"
	_ "image/gif"
	"io"
	"math"
	"os"
	"path/filepath"
	"strings"
)

const (
	allowedURLChars   = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-._~:/?#[]@!$&'()*+,;=%"
	padChar           = "|"
	workerChars       = allowedURLChars + padChar
	magicBitsString   = "10101100010111001101"
	ia                = 18
	ib                = 9
	packetDataBits    = 88
	packetTotalBits   = 20 + 52 + 16
	maxPacketID       = 1000
	defaultJpegQ      = 92
)

var (
	urlCharSet = map[rune]struct{}{}

	magicBits = []uint8{1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1}

	crc16Table [256]uint16

	cosTable [64]float64
	cu       [8]float64
)

func init() {
	for _, r := range allowedURLChars {
		urlCharSet[r] = struct{}{}
	}

	for i := 0; i < 256; i++ {
		curr := uint16(i << 8)
		for j := 0; j < 8; j++ {
			if curr&0x8000 != 0 {
				curr = (curr << 1) ^ 0x1021
			} else {
				curr <<= 1
			}
		}
		crc16Table[i] = curr
	}

	for i := 0; i < 8; i++ {
		for u := 0; u < 8; u++ {
			cosTable[i*8+u] = math.Cos(((2*float64(i) + 1) * float64(u) * math.Pi) / 16)
		}
	}
	cu[0] = 1 / math.Sqrt2
	for i := 1; i < 8; i++ {
		cu[i] = 1
	}
}

func sanitizeURLValue(v string) string {
	var b strings.Builder
	b.Grow(len(v))
	for _, r := range v {
		if _, ok := urlCharSet[r]; ok {
			b.WriteRune(r)
		}
	}
	return b.String()
}

func bitAt(v int, shift int) uint8 {
	return uint8((v >> shift) & 1)
}

func getCRC16(bits []uint8) uint16 {
	crc := uint16(0xFFFF)
	for i := 0; i < len(bits); i += 8 {
		var byteVal uint16
		for j := 0; j < 8 && (i+j) < len(bits); j++ {
			byteVal = (byteVal << 1) | uint16(bits[i+j]&1)
		}
		idx := uint8(((crc >> 8) ^ byteVal) & 0xFF)
		crc = (crc << 8) ^ crc16Table[idx]
	}
	return crc
}

func fwdDCT(blk, out []float64) {
	tmp := make([]float64, 64)
	for r := 0; r < 8; r++ {
		for u := 0; u < 8; u++ {
			s := 0.0
			for x := 0; x < 8; x++ {
				s += blk[r*8+x] * cosTable[x*8+u]
			}
			tmp[r*8+u] = s
		}
	}
	for v := 0; v < 8; v++ {
		for u := 0; u < 8; u++ {
			s := 0.0
			for y := 0; y < 8; y++ {
				s += tmp[y*8+u] * cosTable[y*8+v]
			}
			out[v*8+u] = 0.25 * cu[u] * cu[v] * s
		}
	}
}

func invDCT(dct, out []float64) {
	tmp := make([]float64, 64)
	for y := 0; y < 8; y++ {
		for u := 0; u < 8; u++ {
			s := 0.0
			for v := 0; v < 8; v++ {
				s += cu[v] * dct[v*8+u] * cosTable[y*8+v]
			}
			tmp[y*8+u] = s
		}
	}
	for y := 0; y < 8; y++ {
		for x := 0; x < 8; x++ {
			s := 0.0
			for u := 0; u < 8; u++ {
				s += cu[u] * tmp[y*8+u] * cosTable[x*8+u]
			}
			out[y*8+x] = 0.25 * s
		}
	}
}

type packetBits struct {
	bits []uint8
}

func buildBits(url string) ([]uint8, int, error) {
	numPkt := (len(url) + 5) / 6
	if numPkt == 0 {
		return nil, 0, errors.New("empty url")
	}

	out := make([]uint8, 0, numPkt*packetTotalBits)
	for i := 0; i < numPkt; i++ {
		pkt := make([]uint8, 0, 52)

		for b := 9; b >= 0; b-- {
			pkt = append(pkt, bitAt(i, b))
		}

		for j := 0; j < 6; j++ {
			ch := padChar
			if idx := i*6 + j; idx < len(url) {
				ch = string(url[idx])
			}
			charIdx := strings.IndexRune(workerChars, []rune(ch)[0])
			if charIdx < 0 {
				return nil, 0, fmt.Errorf("INVALID_URL_CHAR: %q", ch)
			}
			for b := 6; b >= 0; b-- {
				pkt = append(pkt, bitAt(charIdx, b))
			}
		}

		crc := getCRC16(pkt)
		crcBits := make([]uint8, 0, 16)
		for b := 15; b >= 0; b-- {
			crcBits = append(crcBits, bitAt(int(crc), b))
		}
		out = append(out, magicBits...)
		out = append(out, pkt...)
		out = append(out, crcBits...)
	}
	return out, numPkt, nil
}

func clampByte(v float64) uint8 {
	if v < 0 {
		return 0
	}
	if v > 255 {
		return 255
	}
	return uint8(math.Round(v))
}

func rgbaAt(pix []uint8, idx int) (r, g, b, a float64) {
	return float64(pix[idx]), float64(pix[idx+1]), float64(pix[idx+2]), float64(pix[idx+3])
}

func encodeImage(img *image.RGBA, url string) (int, error) {
	w, h := img.Bounds().Dx(), img.Bounds().Dy()
	bits, numPkt, err := buildBits(url)
	if err != nil {
		return 0, err
	}

	bX := w / 8
	bY := h / 8
	if bX == 0 || bY == 0 {
		return 0, errors.New("image too small")
	}

	blk := make([]float64, 64)
	dct := make([]float64, 64)
	ibl := make([]float64, 64)
	cur := 0

	pix := img.Pix
	stride := img.Stride

	for by := 0; by < bY*8; by += 8 {
		for bx := 0; bx < bX*8; bx += 8 {
			for y := 0; y < 8; y++ {
				row := (by + y) * stride
				for x := 0; x < 8; x++ {
					p := row + (bx+x)*4
					blk[y*8+x] = 0.299*float64(pix[p]) + 0.587*float64(pix[p+1]) + 0.114*float64(pix[p+2]) - 128
				}
			}

			fwdDCT(blk, dct)
			ac := 0.0
			for k := 1; k < 64; k++ {
				ac += math.Abs(dct[k])
			}
			delta := 10.0
			if ac >= 150 {
				delta = math.Min(85, 25+ac/35)
			}

			bit := bits[cur%len(bits)]
			cur++

			aA := math.Abs(dct[ia])
			aB := math.Abs(dct[ib])
			if bit == 1 {
				if aA-aB < delta {
					avg := (aA + aB) / 2
					aA = avg + delta/2
					aB = math.Max(0, avg-delta/2)
				}
			} else {
				if aB-aA < delta {
					avg := (aA + aB) / 2
					aB = avg + delta/2
					aA = math.Max(0, avg-delta/2)
				}
			}

			if dct[ia] >= 0 {
				dct[ia] = aA
			} else {
				dct[ia] = -aA
			}
			if dct[ib] >= 0 {
				dct[ib] = aB
			} else {
				dct[ib] = -aB
			}

			invDCT(dct, ibl)
			for y := 0; y < 8; y++ {
				row := (by + y) * stride
				for x := 0; x < 8; x++ {
					p := row + (bx+x)*4
					oldGray := 0.299*float64(pix[p]) + 0.587*float64(pix[p+1]) + 0.114*float64(pix[p+2]) - 128
					d := ibl[y*8+x] - oldGray
					pix[p] = clampByte(float64(pix[p]) + d)
					pix[p+1] = clampByte(float64(pix[p+1]) + d)
					pix[p+2] = clampByte(float64(pix[p+2]) + d)
					// alpha unchanged
				}
			}
		}
	}
	return numPkt, nil
}

type decodeResult struct {
	chunks map[int]string
	maxID  int
}

func decodeImage(img *image.RGBA) decodeResult {
	w, h := img.Bounds().Dx(), img.Bounds().Dy()

	chunks := make(map[int]string)
	maxID := -1

	blk := make([]float64, 64)
	dct := make([]float64, 64)

	pix := img.Pix
	stride := img.Stride

	for oy := 0; oy < 8; oy++ {
		for ox := 0; ox < 8; ox++ {
			bX := (w - ox) / 8
			bY := (h - oy) / 8
			if bX < 10 {
				continue
			}
			bits := make([]uint8, bX*bY)
			bi := 0

			for by := oy; by < oy+bY*8; by += 8 {
				for bx := ox; bx < ox+bX*8; bx += 8 {
					for y := 0; y < 8; y++ {
						row := (by + y) * stride
						for x := 0; x < 8; x++ {
							p := row + (bx+x)*4
							blk[y*8+x] = 0.299*float64(pix[p]) + 0.587*float64(pix[p+1]) + 0.114*float64(pix[p+2]) - 128
						}
					}
					fwdDCT(blk, dct)
					if math.Abs(dct[ia]) > math.Abs(dct[ib]) {
						bits[bi] = 1
					} else {
						bits[bi] = 0
					}
					bi++
				}
			}

			i := 0
			for i <= len(bits)-packetDataBits {
				match := true
				for m := 0; m < len(magicBits); m++ {
					if bits[i+m] != magicBits[m] {
						match = false
						break
					}
				}
				if !match {
					i++
					continue
				}

				pktBits := bits[i+20 : i+20+52]
				crcIn := getCRC16(pktBits)

				var crcSaved uint16
				for b := 0; b < 16; b++ {
					crcSaved = (crcSaved << 1) | uint16(bits[i+72+b]&1)
				}

				if crcIn == crcSaved {
					id := 0
					for b := 0; b < 10; b++ {
						id = (id << 1) | int(pktBits[b]&1)
					}

					if id < maxPacketID {
						var payload strings.Builder
						payload.Grow(6)
						for j := 0; j < 6; j++ {
							ci := 0
							for k := 0; k < 7; k++ {
								ci = (ci << 1) | int(pktBits[10+j*7+k]&1)
							}
							payload.WriteByte(workerChars[ci%len(workerChars)])
						}
						if _, ok := chunks[id]; !ok {
							chunks[id] = payload.String()
							if id > maxID {
								maxID = id
							}
						}
						i += packetDataBits
						continue
					}
				}
				i++
			}
		}
	}

	return decodeResult{chunks: chunks, maxID: maxID}
}

func concatChunks(res decodeResult) string {
	if res.maxID < 0 {
		return ""
	}
	var b strings.Builder
	for i := 0; i <= res.maxID; i++ {
		if s, ok := res.chunks[i]; ok {
			b.WriteString(s)
		}
	}
	return strings.TrimRight(b.String(), padChar)
}

func decodeToRGBA(src image.Image) *image.RGBA {
	b := src.Bounds()
	dst := image.NewRGBA(b)
	draw.Draw(dst, b, src, b.Min, draw.Src)
	return dst
}

func openImage(path string) (image.Image, string, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, "", err
	}
	defer f.Close()
	img, format, err := image.Decode(f)
	if err != nil {
		return nil, "", err
	}
	return img, format, nil
}

func saveImage(path, format string, img image.Image, quality int) error {
	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()

	switch strings.ToLower(format) {
	case "png":
		return png.Encode(f, img)
	case "jpg", "jpeg":
		opt := &jpeg.Options{Quality: quality}
		return jpeg.Encode(f, img, opt)
	default:
		return fmt.Errorf("unsupported format: %s", format)
	}
}

func ensureOutputPath(out, fallbackFormat string) string {
	if out != "" {
		return out
	}
	return "output." + fallbackFormat
}

func readAllStdin() (string, error) {
	b, err := io.ReadAll(os.Stdin)
	if err != nil {
		return "", err
	}
	return string(b), nil
}

func main() {
	if len(os.Args) < 2 {
		fmt.Fprintf(os.Stderr, "usage:\n  %s encode -in input.png -out output.png -url 'https://example.com' [-format png|jpg] [-quality 92]\n  %s decode -in image.png\n", filepath.Base(os.Args[0]), filepath.Base(os.Args[0]))
		os.Exit(2)
	}

	switch os.Args[1] {
	case "encode":
		fs := flag.NewFlagSet("encode", flag.ExitOnError)
		inPath := fs.String("in", "", "input image path")
		outPath := fs.String("out", "", "output image path")
		url := fs.String("url", "", "url to embed")
		format := fs.String("format", "png", "output format: png or jpg")
		quality := fs.Int("quality", defaultJpegQ, "jpeg quality (1-100)")
		fs.Parse(os.Args[2:])

		if *url == "" {
			fmt.Fprintln(os.Stderr, "missing -url")
			os.Exit(2)
		}

		if *inPath == "" {
			fmt.Fprintln(os.Stderr, "missing -in")
			os.Exit(2)
		}

		if *outPath == "" {
			*outPath = ensureOutputPath("", *format)
		}

		imgSrc, _, err := openImage(*inPath)
		if err != nil {
			fmt.Fprintln(os.Stderr, "open input:", err)
			os.Exit(1)
		}
		rgba := decodeToRGBA(imgSrc)

		sanitized := sanitizeURLValue(strings.TrimSpace(*url))
		if sanitized != strings.TrimSpace(*url) {
			fmt.Fprintln(os.Stderr, "warning: non-standard URL chars were removed; using sanitized value")
		}
		if sanitized == "" {
			fmt.Fprintln(os.Stderr, "empty URL after sanitization")
			os.Exit(2)
		}

		total, err := encodeImage(rgba, sanitized)
		if err != nil {
			fmt.Fprintln(os.Stderr, "encode:", err)
			os.Exit(1)
		}

		if *quality < 1 {
			*quality = 1
		}
		if *quality > 100 {
			*quality = 100
		}
		if err := saveImage(*outPath, *format, rgba, *quality); err != nil {
			fmt.Fprintln(os.Stderr, "save:", err)
			os.Exit(1)
		}

		fmt.Printf("encoded ok: %s (packets=%d)\n", *outPath, total)

	case "decode":
		fs := flag.NewFlagSet("decode", flag.ExitOnError)
		inPath := fs.String("in", "", "input image path")
		fs.Parse(os.Args[2:])

		if *inPath == "" {
			fmt.Fprintln(os.Stderr, "missing -in")
			os.Exit(2)
		}

		imgSrc, _, err := openImage(*inPath)
		if err != nil {
			fmt.Fprintln(os.Stderr, "open input:", err)
			os.Exit(1)
		}
		rgba := decodeToRGBA(imgSrc)
		res := decodeImage(rgba)
		out := concatChunks(res)

		if out == "" {
			fmt.Println("")
			fmt.Fprintln(os.Stderr, "no valid watermark found")
			os.Exit(1)
		}
		fmt.Println(out)

	default:
		fmt.Fprintf(os.Stderr, "unknown command: %s\n", os.Args[1])
		os.Exit(2)
	}
}

// Useful to avoid unused import warnings in some environments that strip code paths.
var _ color.Color
