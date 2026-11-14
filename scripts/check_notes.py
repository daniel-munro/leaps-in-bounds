"""Check that search notes in notes/ are plain, visible Markdown.

Notes are written by anyone and read by people and AI agents, so this rejects
anything that could hide content from a reviewer reading the diff or the
rendered file. See notes/README.md.
"""

import re
import sys
import unicodedata
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
NOTES = ROOT / 'notes'
MAX_BYTES = 50_000
MAX_RUN = 200
ALLOWED_CONTROL = {'\n', '\t'}

FENCE = re.compile(r'^ {0,3}(`{3,}|~{3,}).*?^ {0,3}\1[`~]*[ \t]*$', re.MULTILINE | re.DOTALL)
UNCLOSED_FENCE = re.compile(r'^ {0,3}(`{3,}|~{3,}).*\Z', re.MULTILINE | re.DOTALL)
INLINE_CODE = re.compile(r'(`+)(?!`).*?(?<!`)\1(?!`)', re.DOTALL)
HTML = re.compile(r'<\s*(?:!|\?|/?\s*[A-Za-z][\w:-]*(?:\s|/?>|$))', re.MULTILINE)
IMAGE = re.compile(r'!\[')
# Inline links [text](target) and reference definitions [label]: target
LINK_TARGET = re.compile(r'\]\(\s*<?([^)\s>]*)|^ {0,3}\[[^\]]+\]:\s*<?(\S*?)>?(?:\s|$)', re.MULTILINE)
AUTOLINK_SCHEME = re.compile(r'^[A-Za-z][A-Za-z0-9+.-]*:')
# Text that reads as addressed to an AI agent. Only warns: a reviewer decides.
AGENT_DIRECTED = re.compile(
    r'ignore (?:all |any )?(?:the )?(?:previous|prior|above|earlier) |'
    r'system prompt|\bAGENTS\.md\b|\bCLAUDE\.md\b|\.claude/|'
    r'\b(?:AI|LLM|language model|assistant|agent)s?,? (?:must|should|shall|need to)\b|'
    r'\byou (?:must|are required to) (?:run|execute|install|download|open|send|commit|push)\b|'
    r'</?(?:system|instructions?|user|assistant)>',
    re.IGNORECASE,
)


def blank(m: re.Match) -> str:
    return re.sub(r'[^\n]', ' ', m.group())


def strip_code(text: str) -> str:
    """Blank out fenced and inline code, which render as literal text, keeping line numbers."""
    text = FENCE.sub(blank, text)
    text = UNCLOSED_FENCE.sub(blank, text)
    return INLINE_CODE.sub(blank, text)


def line_of(text: str, index: int) -> int:
    return text.count('\n', 0, index) + 1


def check_file(path: Path, errors: list[str], warnings: list[str]) -> None:
    name = path.relative_to(ROOT)
    data = path.read_bytes()
    if len(data) > MAX_BYTES:
        errors.append(f'{name}: {len(data)} bytes, over the limit of {MAX_BYTES}')
    try:
        text = data.decode('utf-8')
    except UnicodeDecodeError as e:
        errors.append(f'{name}: not valid UTF-8 ({e})')
        return

    for i, ch in enumerate(text):
        category = unicodedata.category(ch)
        if ch in ALLOWED_CONTROL:
            continue
        if category in ('Cc', 'Cf', 'Co', 'Cs', 'Cn') or (category in ('Zl', 'Zp')) \
                or (category == 'Zs' and ch != ' '):
            label = unicodedata.name(ch, f'U+{ord(ch):04X}')
            errors.append(f'{name}:{line_of(text, i)}: invisible or control character {label}')

    for m in re.finditer(r'\S{%d,}' % (MAX_RUN + 1), text):
        errors.append(f'{name}:{line_of(text, m.start())}: {len(m.group())} characters without '
                      'whitespace (encoded data or witnesses belong elsewhere)')

    # Markup checks apply outside code, where Markdown renders it instead of showing it
    prose = strip_code(text)
    for m in HTML.finditer(prose):
        errors.append(f'{name}:{line_of(prose, m.start())}: HTML is not allowed: {m.group().strip()!r}')
    for m in IMAGE.finditer(prose):
        errors.append(f'{name}:{line_of(prose, m.start())}: images are not allowed')
    for m in LINK_TARGET.finditer(prose):
        target = m.group(1) if m.group(1) is not None else m.group(2)
        if AUTOLINK_SCHEME.match(target) and not target.lower().startswith(('http://', 'https://')):
            errors.append(f'{name}:{line_of(prose, m.start())}: link target {target!r} is not http(s) or a relative path')

    if path.name == 'README.md':
        return
    for m in AGENT_DIRECTED.finditer(text):
        warnings.append(f'{name}:{line_of(text, m.start())}: reads as addressed to an AI agent, '
                        f'please review: {m.group()!r}')


def main() -> int:
    if not NOTES.exists():
        return 0
    with open(ROOT / 'constants' / 'families.yml') as f:
        families = set(yaml.safe_load(f))
    allowed = {'README.md', 'general.md'} | {f'{g}.md' for g in families}

    errors: list[str] = []
    warnings: list[str] = []
    for path in sorted(NOTES.rglob('*')):
        name = path.relative_to(ROOT)
        if path.is_symlink():
            errors.append(f'{name}: symlinks are not allowed')
        elif path.is_dir():
            errors.append(f'{name}: subdirectories are not allowed')
        elif path.parent != NOTES or path.name not in allowed:
            errors.append(f'{name}: notes must be notes/<family>.md for a family in '
                          'constants/families.yml, or notes/general.md')
        else:
            check_file(path, errors, warnings)

    for w in warnings:
        print(f'Warning: {w}')
    for e in errors:
        print(f'Error: {e}')
    if errors:
        return 1
    count = sum(1 for p in NOTES.glob('*.md') if p.name != 'README.md')
    print(f'Checked {count} notes files')
    return 0


if __name__ == '__main__':
    sys.exit(main())
