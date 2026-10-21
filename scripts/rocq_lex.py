#!/usr/bin/env python3
"""Read the text of a .v file as Rocq 9.1.1 reads comments, strings and
blanks.

The checks of scripts/check_sources.py compare and scan the code of .v
files: the text without its comments. This module gives them the code that
Rocq reads. It follows the lexer of Rocq 9.1.1 (parsing/cLexer.ml) and the
reference manual, section "Lexical conventions":

- the blanks are space, tab, newline and carriage return; every other
  character, form feed and U+00A0 among them, belongs to a token;
- Rocq skips one byte order mark, U+FEFF, at the start of a file, so a
  U+FEFF at index 0 is a blank here; anywhere else it belongs to a token;
- a comment opens with (* and closes with the matching *); comments nest,
  and (*) opens a comment;
- a string opens and closes with a double quote, and two double quotes
  inside it stand for one; (* and *) inside a string have no effect;
- inside a comment, a double quote opens a string as in code, so a *)
  inside that string does not close the comment, and a (* inside it opens
  no comment;
- a comment separates tokens, as a blank does.

Rocq reads (* as a comment, and a double quote as a string, only where a
token starts. When one of them follows a token with no blank or comment
between, the keywords in scope decide. Rocq declares the keyword .(, so in
0.(* the dot and the parenthesis are one token; MathComp-Analysis declares
_(, so in fun _(* the (* opens no comment either; and a Notation can
declare a symbol that holds (* or a double quote. In the same way, :{{
after an identifier, a number or a string, and the keyword lp: of Elpi
(which HB loads) before (, [ or {, open a quotation, whose text Rocq reads
raw: a (* or a double quote inside it opens nothing. This module does not
know the keywords in scope. It raises LexError on these three forms
rather than guess.

It also raises LexError on a string inside a comment that holds a *)
closing no (* of the string. Rocq reads that comment as this module does,
but warns (comment-terminator-in-string), and Set Warnings, a required
module or the command line can make the warning an error: the comment
would then decide whether the file compiles.

segments, strip_comments, code and non_ascii take the whole text of a
file. They raise LexError for an unterminated comment or string and for
these four forms. Lines and columns count from 1, columns in characters.

read_source reads a file as Rocq does: UTF-8, with the carriage returns
kept. Path.read_text() and git show with text=True turn \\r\\n into \\n,
also inside strings, where Rocq keeps the carriage return; this module
reads files only through read_source. decode_source decodes bytes, such as
the output of git show, in the same way. Both raise LexError on bytes that
are not UTF-8, also inside a comment, where Rocq accepts any byte.
"""

import re

BLANKS = " \t\n\r"
BYTE_ORDER_MARK = "\ufeff"

UNTERMINATED_COMMENT = "unterminated comment"
UNTERMINATED_STRING = "unterminated string"
GLUED_COMMENT = ("(* follows a token with no blank between, and a keyword in "
                 "scope may continue that token with (")
GLUED_STRING = ("a double quote follows a token with no blank between, and a "
                "keyword in scope may continue that token with it")
QUOTATION = ("a quotation (:{{, or lp: before (, [ or {), whose text Rocq "
             "reads raw")
TERMINATOR_IN_STRING = ("a *) in a string inside a comment closes no (* of "
                        "the string, and Rocq warns there "
                        "(comment-terminator-in-string), a warning that may "
                        "be an error")
INVALID_UTF8 = "bytes that are not valid UTF-8"

_BLANK_END = re.compile(r"[^ \t\n\r]")
_CODE_END = re.compile(r'[ \t\n\r"]|\(\*')
_DELIMITER = re.compile(r"\(\*|\*\)")
_COMMENT_MARK = re.compile(r'\(\*|\*\)|"')
_QUOTATION_START = re.compile(r":\{\{|lp:[(\[{]")
_NON_ASCII = re.compile(r"[^\x00-\x7f]")


class LexError(Exception):
    """An unterminated comment or string, a form that Rocq reads by the
    keywords in scope or by the warnings in force, or bytes that are not
    UTF-8. line and column locate it; reason is one of the seven constants
    of this module."""

    def __init__(self, text, index, reason):
        line = text.count("\n", 0, index) + 1
        column = index - text.rfind("\n", 0, index)
        super().__init__(f"line {line}, column {column}: {reason}")
        self.line, self.column, self.reason = line, column, reason


def _string_end(text, start):
    """The index just after the string whose opening quote is at start."""
    i = start + 1
    while True:
        i = text.find('"', i)
        if i < 0:
            raise LexError(text, start, UNTERMINATED_STRING)
        if not text.startswith('""', i):
            return i + 1
        i += 2


def _check_string_in_comment(text, start, end):
    """Raise LexError if the string text[start:end], which sits in a
    comment, holds a *) that closes no (* of the string. Rocq counts them
    from the opening quote as here, and warns at such a *)."""
    level = 0
    for mark in _DELIMITER.finditer(text, start + 1, end - 1):
        if mark.group() == "(*":
            level += 1
        elif level == 0:
            raise LexError(text, mark.start(), TERMINATOR_IN_STRING)
        else:
            level -= 1


def _comment_end(text, start):
    """The index just after the comment that opens at start."""
    depth, i = 1, start + 2
    while True:
        mark = _COMMENT_MARK.search(text, i)
        if mark is None:
            raise LexError(text, start, UNTERMINATED_COMMENT)
        i = mark.end()
        if mark.group() == "(*":
            depth += 1
        elif mark.group() == "*)":
            depth -= 1
            if depth == 0:
                return i
        else:
            i = _string_end(text, mark.start())
            _check_string_in_comment(text, mark.start(), i)


def _pieces(text):
    """The (kind, start, end) of the pieces of text, in order."""
    pieces, i, n = [], 0, len(text)
    after_token = False
    while i < n:
        if text[i] in BLANKS or (i == 0 and text[i] == BYTE_ORDER_MARK):
            end = _BLANK_END.search(text, i + 1)
            j = end.start() if end else n
            kind, after_token = "blank", False
        elif text.startswith("(*", i):
            if after_token:
                raise LexError(text, i, GLUED_COMMENT)
            j = _comment_end(text, i)
            kind, after_token = "comment", False
        elif text[i] == '"':
            if after_token:
                raise LexError(text, i, GLUED_STRING)
            j = _string_end(text, i)
            kind, after_token = "string", True
        else:
            end = _CODE_END.search(text, i)
            j = end.start() if end else n
            quotation = _QUOTATION_START.search(text, i, j)
            if quotation:
                raise LexError(text, quotation.start(), QUOTATION)
            kind, after_token = "code", True
        pieces.append((kind, i, j))
        i = j
    return pieces


def segments(text):
    """The pieces of text, as pairs (kind, piece) whose pieces concatenate
    to text. kind is blank (a maximal run of blanks, the U+FEFF at index 0
    included), comment (a whole outermost comment, with the comments and
    strings inside it), string (a string of the code, with its quotes) or
    code (a maximal run of the other characters)."""
    return [(kind, text[i:j]) for kind, i, j in _pieces(text)]


def strip_comments(text):
    """text with each comment replaced by one space and the rest
    unchanged."""
    return "".join(" " if kind == "comment" else piece
                   for kind, piece in segments(text))


def code(text):
    """The code of text: each maximal run of blanks and comments becomes
    one space, a run at the end is dropped, and so is a run at the start,
    unless a U+FEFF follows it (at index 0 Rocq would skip that U+FEFF);
    the strings (their blanks too) and the other characters are kept as
    they are."""
    out, gap = [], False
    for kind, piece in segments(text):
        if kind in ("blank", "comment"):
            gap = True
            continue
        if gap and (out or piece.startswith(BYTE_ORDER_MARK)):
            out.append(" ")
        out.append(piece)
        gap = False
    return "".join(out)


def non_ascii(text):
    """The (line, column, character) of each non-ASCII character outside
    the comments of text, in order, the U+FEFF at index 0 included."""
    found, line, line_start, seen = [], 1, 0, 0
    for kind, i, j in _pieces(text):
        if kind == "comment":
            continue
        for char in _NON_ASCII.finditer(text, i, j):
            k = char.start()
            line += text.count("\n", seen, k)
            newline = text.rfind("\n", seen, k)
            if newline >= 0:
                line_start = newline + 1
            seen = k
            found.append((line, k - line_start + 1, char.group()))
    return found


def decode_source(data):
    """The text of the bytes data of a .v file: UTF-8, with the carriage
    returns kept. The LexError for bytes that are not UTF-8 locates the
    first of them."""
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError as error:
        valid = data[:error.start].decode("utf-8")
        raise LexError(valid, len(valid), INVALID_UTF8) from None


def read_source(path):
    """The text of the file at path, decoded by decode_source."""
    with open(path, "rb") as source:
        return decode_source(source.read())
