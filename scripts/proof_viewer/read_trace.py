"""Read a trace in contiguous character pages without dropping long records."""
import argparse
from pathlib import Path


def read_page(text, offset, size):
    if not 0 <= offset <= len(text) or size <= 0:
        raise ValueError('Offset must be within the file; size must be positive')
    end = min(offset + size, len(text))
    return text[offset:end], end


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('offset', type=int)
    parser.add_argument('--size', type=int, default=12000)
    args = parser.parse_args()
    text = Path('full_trace.json').read_text(encoding='utf-8')
    body, end = read_page(text, args.offset, args.size)
    print(f'Characters [{args.offset}, {end}) of {len(text)}')
    print(body)
    print('END_OF_TRACE' if end == len(text) else f'next_offset: {end}')


if __name__ == '__main__':
    main()
