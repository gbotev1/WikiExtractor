#!/usr/bin/env python3
# -*- coding: utf-8 -*-
#
# Modified by Georgie Botev in March 2021.
#
# Incubator module added by Grzegorz Stark for Apertium, in December 2017.
#
# And changed even more by Ben Stobaugh for Apertium, in December 2013.
#
# Hacked up by Alex Rudnick for use in Guampa, October 2013.
#
# =============================================================================
#  Version: 2.5 (May 9, 2013)
#  Author: Giuseppe Attardi (attardi@di.unipi.it), University of Pisa
#      Antonio Fuschetto (fuschett@di.unipi.it), University of Pisa
#
#  Contributors:
#   Leonardo Souza (lsouza@amtera.com.br)
#   Juan Manuel Caicedo (juan@cavorite.com)
#   Humberto Pereira (begini@gmail.com)
#   Siegfried-A. Gevatter (siegfried@gevatter.com)
#   Pedro Assis (pedroh2306@gmail.com)
#
# =============================================================================
#  Copyright (c) 2009. Giuseppe Attardi (attardi@di.unipi.it).
# =============================================================================
#  This file is part of Tanl.
#
#  Tanl is free software; you can redistribute it and/or modify it
#  under the terms of the GNU General Public License, version 3,
#  as published by the Free Software Foundation.
#
#  Tanl is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS f A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program.  If not, see <http://www.gnu.org/licenses/>.
# =============================================================================

import re
from bz2 import BZ2File
from mimetypes import guess_type
from os import path
from html.entities import name2codepoint
from argparse import ArgumentParser, ArgumentDefaultsHelpFormatter
from typing import TextIO
from string import punctuation

# For status updates
counter = 0

# This is obtained from the dump itself.
prefix = None

# Drop these elements from article text
discard_elements = {'gallery', 'timeline', 'noinclude', 'pre', 'table', 'tr', 'td', 'th', 'caption', 'form', 'input',
                    'select', 'option', 'textarea', 'ul', 'li', 'ol', 'dl', 'dt', 'dd', 'menu', 'dir', 'ref',
                    'references', 'img', 'imagemap', 'source'}

# PATTERNS
discard_element_patterns = []
ignored_tag_patterns = []
self_closing_tag_patterns = []
placeholder_tag_patterns = []

# TAGS
self_closing_tags = ['br', 'hr', 'nobr', 'ref', 'references']
ignored_tags = [
    'a', 'b', 'big', 'blockquote', 'center', 'cite', 'div', 'em',
    'font', 'h1', 'h2', 'h3', 'h4', 'hiero', 'i', 'kbd', 'nowiki',
    'p', 'plaintext', 's', 'small', 'span', 'strike', 'strong',
    'sub', 'sup', 'tt', 'u', 'var',
]
placeholder_tags = {'math': '<<MATH>>', 'code': '<<CODE>>'}

# REGEXES
PREFORMATTED = re.compile(r'^ .*?$', re.MULTILINE)
EXTERNAL_LINK = re.compile(r'\[\w+.*? (.*?)]')  # Space separates second optional parameter
EXTERNAL_LINK_NO_ANCHOR = re.compile(r'\[\w+[&\]]*]')
BOLD_ITALIC = re.compile(r"'''''([^']*?)'''''")
BOLD = re.compile(r"'''(.*?)'''")
ITALIC_QUOTE = re.compile(r"''\"(.*?)\"''")
ITALIC = re.compile(r"''([^']*)''")
QUOTE_QUOTE = re.compile(r'""(.*?)""')
SPACES = re.compile(r' {2,}')
DOTS = re.compile(r'\.{4,}')
PARAMETRIZED_LINK = re.compile(r'(?:\[\[.*\|)|(?:]])')
COMMENT = re.compile(r'<!--.*?-->', re.DOTALL)
TAGS = re.compile(r'(.*?)<(/?\w+)[^>]*>(?:([^<]*)(<.*?>)?)?')
TITLE = re.compile(r'[\s_]+')
TITLE_MATCH = re.compile(r'([^:]*):(\s*)(\S(?:.*))')
SECTION = re.compile(r'(==+)\s*(.*?)\s*\1')
PUNCTUATION = re.compile(r'\n[{}]+?\n'.format(punctuation))  # More robust cross-lingual variant of `\W`
UNDERSCORE_NAME = re.compile(r'__[^\d\W]+__')  # Non-digit + non-non-word = word + non-digit
RIGHT_HEAVY_DASHED_PARENTHETICALS = re.compile(r'(?<=\() - (?=.*\))')
COMMAS = re.compile(r',{2,}')
PLACEHOLDER_TAGS = re.compile(r'<<(?:MATH|CODE)>>_\d*')
QUOTES = re.compile(r'[\u2018-\u201f]')
DUPLICATE_QUOTES = re.compile(r'\"{2,}')
EMPTY_BRACKETS = re.compile(r'(?:\(\))|(?:\[])')
EMPTY_COMMAS = re.compile(r',(?: ,)+')
LONE_COMMA_LEFT = re.compile(r'\s?,\s?\)')
LONE_COMMA_RIGHT = re.compile(r'\(\s?,\s?')
BAD_LINKS = re.compile(r'(?:\n\w+?(?:\|.+?)+?\n)|(?:\n\w+?:.+?\n)')
# Matches non-breaking hyphen, figure dash, en dash, em dash, horizontal bar, two-em dash, and three-em dash
DASHES = re.compile(r'[\u2011-\u2015⸺⸻]')
MULTIPLE_NEWLINES = re.compile(r'\n{2,}')
# Match inter-wiki links, | separates parameters.
# First parameter is displayed, also trailing concatenated text included in display, e.g. s for plural.
# Can be nested [[File:..|..[[..]]..|..]], [[Category:...]], etc.
# We first expand inner ones, then remove enclosing ones.
WIKI_LINK = re.compile(r'\[\[([^[]*?)(?:\|([^[]*?))?]](\w*)')


def normalize_title(title: str) -> str:
    # Remove leading whitespace and underscores
    title = title.strip(' _')
    # Replace sequences of whitespace and underscore chars with a single space
    title = TITLE.sub(' ', title)
    m = TITLE_MATCH.match(title)
    if m:
        prefix_shadow = m.group(1)
        if m.group(2):
            optional_whitespace = ' '
        else:
            optional_whitespace = ''
        rest = m.group(3)
        return f'{prefix_shadow.capitalize()}:{optional_whitespace}{rest}'
    else:
        # No namespace, so just capitalize first letter
        return title.capitalize()


# Removes HTML or XML character references and entities from a text string.
# @param text The HTML (or XML) source text.
# @return The plain text, as a Unicode string, if necessary.
def unescape(text: str) -> str:
    def fixup(m: re.Match) -> str:
        text_inner = m.group(0)
        code = m.group(1)
        if text_inner[1] == '#':
            # Character reference
            if text_inner[2] == 'x':
                return chr(int(code[1:], 16))
            else:
                return chr(int(code))
        elif code in name2codepoint:
            # Named entity
            return chr(name2codepoint[code])
        else:
            # Leave as-is
            return text_inner

    return re.sub(r'&#?(\w+);', fixup, text)


def drop_nested(text: str, open_delim: str, close_delim: str) -> str:
    """A matching function for nested expressions, e.g. namespaces and tables."""
    open_re = re.compile(open_delim)
    close_re = re.compile(close_delim)
    # Partition text in separate blocks { } { }
    matches = []  # Pairs (s, e) for each partition
    nest = 0  # Nesting level
    start = open_re.search(text, 0)
    if not start:
        return text
    end = close_re.search(text, start.end())
    next_shadow = start
    while end:
        next_shadow = open_re.search(text, next_shadow.end())
        if not next_shadow:  # termination
            while nest:  # close all pending
                nest -= 1
                end0 = close_re.search(text, end.end())
                if end0:
                    end = end0
                else:
                    break
            matches.append((start.start(), end.end()))
            break
        while end.end() < next_shadow.start():
            # { } {
            if nest:
                nest -= 1
                # try closing more
                last = end.end()
                end = close_re.search(text, end.end())
                if not end:  # unbalanced
                    if matches:
                        span = (matches[0][0], last)
                    else:
                        span = (start.start(), last)
                    matches = [span]
                    break
            else:
                matches.append((start.start(), end.end()))
                # advance start, find next close
                start = next_shadow
                end = close_re.search(text, next_shadow.end())
                break  # { }
        if next_shadow != start:
            # { { }
            nest += 1
    # Collect text outside partitions
    res = ''
    start = 0
    for s, e in matches:
        res += text[start:s]
        start = e
    res += text[start:]
    return res


def drop_spans(matches, text: str) -> str:
    """Drop text from blocks identified in matches."""
    matches.sort()
    res = ''
    start = 0
    for s, e in matches:
        res += text[start:s]
        start = e
    res += text[start:]
    return res


def make_anchor_tag(match: re.Match) -> str:
    """Function applied to WIKI_LINK's."""
    link = match.group(1)
    trail = match.group(3)
    anchor = match.group(2)
    if not anchor:
        anchor = link
    anchor += trail
    return anchor


def clean(text: str) -> str:
    # FIXME: templates should be expanded
    # Drop transclusions (template, parser functions)
    # See: http://www.mediawiki.org/wiki/Help:Templates
    text = drop_nested(text, r'{{', r'}}')

    # Drop tables
    text = drop_nested(text, r'{\|', r'\|}')

    # Expand links
    text = WIKI_LINK.sub(make_anchor_tag, text)
    # Drop all remaining ones (except link text)
    text = PARAMETRIZED_LINK.sub('', text)

    # Handle external links
    text = EXTERNAL_LINK.sub(r'\1', text)
    text = EXTERNAL_LINK_NO_ANCHOR.sub('', text)

    # Handle bold/italic/quote
    text = BOLD_ITALIC.sub(r'\1', text)
    text = BOLD.sub(r'\1', text)
    text = ITALIC_QUOTE.sub(r'&quot;\1&quot;', text)
    text = ITALIC.sub(r'&quot;\1&quot;', text)
    text = QUOTE_QUOTE.sub(r'\1', text)
    text = text.replace("'''", '').replace("''", '&quot;')

    # Process HTML
    # Turn into HTML
    text = unescape(text)
    # Do it again (&amp;nbsp;)
    text = unescape(text)

    # Collect spans
    matches = []
    # Drop HTML comments
    for m in COMMENT.finditer(text):
        matches.append((m.start(), m.end()))

    # Drop self-closing tags
    for pattern_shadow in self_closing_tag_patterns:
        for m in pattern_shadow.finditer(text):
            matches.append((m.start(), m.end()))

    # Drop ignored tags
    for left, right in ignored_tag_patterns:
        for m in left.finditer(text):
            matches.append((m.start(), m.end()))
        for m in right.finditer(text):
            matches.append((m.start(), m.end()))

    # Bulk remove all spans
    text = drop_spans(matches, text)

    # Drop discarded elements: can't use dropSpan on these since they may be nested
    for pattern_shadow in discard_element_patterns:
        text = pattern_shadow.sub('', text)

    # Expand placeholders
    for pattern_shadow, placeholder in placeholder_tag_patterns:
        for i, match in enumerate(pattern_shadow.finditer(text)):
            text = text.replace(match.group(), f'{placeholder}_{i + 1}')

    # Drop preformatted: this can't be done before since it may remove tags
    text = PREFORMATTED.sub('', text)

    # Cleanup text
    # One-time
    text = text.replace('\t', ' ')  # Replace TAB with space
    text = text.replace(u'\xa0', ' ')  # Replace NBSP with regular space
    text = DASHES.sub('-', text)  # Replace all dash varieties with `-`
    text = QUOTES.sub('"', text)  # Normalize quotation characters with `"`
    text = PLACEHOLDER_TAGS.sub('', text)  # Remove all placeholder tags (math/code)
    # Repeat until no change
    old_text_len = -1
    new_text_len = 0
    while old_text_len != new_text_len:  # Always enter at least once!
        # Update old text length
        old_text_len = len(text)
        text = SPACES.sub(' ', text)  # Replace more than 2 spaces with 1
        text = DOTS.sub('...', text)  # Replace more than 4 dots with 3
        text = PUNCTUATION.sub('\n', text)  # Lines with only punctuation
        text = UNDERSCORE_NAME.sub('', text)  # Instances of form: `__[capital letter but not digit]__`
        text = RIGHT_HEAVY_DASHED_PARENTHETICALS.sub('', text)  # Transform instances of `( - [text])` into `([text])`
        text = BAD_LINKS.sub('', text)  # Remove bad links of form `...|...|...` (etc)
        text = DUPLICATE_QUOTES.sub('"', text)  # Replace two or more consecutive quotes with just one
        text = EMPTY_BRACKETS.sub('', text)  # Remove empty bracket statements
        text = text.replace('..', '.')  # Reduce two periods to a singular one
        text = COMMAS.sub(',', text).replace(',.', '.').replace('.,.', '.')  # Fix weird comma patterns
        text = EMPTY_COMMAS.sub(',', text)  # Replace empty comma-delimited expressions with a singular comma
        # Remove lone, dangling commas inside parenthetical statements
        text = LONE_COMMA_LEFT.sub('(', text)
        text = LONE_COMMA_RIGHT.sub(')', text)
        text = text.replace(' .', '.')  # Re-space spaced periods
        text = text.replace(' ,', ',')  # Re-space spaced commas
        text = MULTIPLE_NEWLINES.sub('\n', text)  # Replace instances of two or more line feeds with a singular one
        # Update new text length
        new_text_len = len(text)
    return text


def compact(text: str, structure: bool = False) -> list[str]:
    """Deal with headers, lists, empty sections, residuals of tables."""
    page = []  # List of paragraphs
    headers = {}  # Headers for unfilled sections
    empty_section = False  # Empty sections are discarded

    for line in text.split('\n'):
        if not line:
            continue
        # Handle section titles
        m = SECTION.match(line)
        if m:
            title = m.group(2)
            lev = len(m.group(1))
            if structure:
                page.append(f'<h{lev}>{title}</h{lev}>')
            if title and title[-1] not in '!?':
                title += '.'
            headers[lev] = title
            # drop previous headers
            for i in list(headers.keys()):
                if i > lev:
                    del headers[i]
            empty_section = True
            continue
        # Handle page title
        if line.startswith('++'):
            title = line[2:-2]
            if title:
                if title[-1] not in '!?':
                    title += '.'
                page.append(title)
        # handle lists
        elif line[0] in '*#:;':
            if structure:
                page.append(f'<li>{line[1:]}</li>')
            else:
                continue
        # Drop residuals of lists
        elif line[0] in '{|' or line[-1] in '}':
            continue
        # Drop irrelevant lines
        elif (line[0] == '(' and line[-1] == ')') or line.strip('.-') == '':
            continue
        elif len(headers):
            items = list(headers.items())
            items.sort()
            for (i, v) in items:
                page.append(v)
            headers.clear()
            page.append(line)  # First line
            empty_section = False
        elif not empty_section:
            page.append(line)

    return page


def handle_unicode(entity: str) -> str:
    numeric_code = int(entity[2:-1])
    if numeric_code >= 0x10000:
        return ''
    return chr(numeric_code)


def wiki_document_sentences(outfile: TextIO, title: str, text: str) -> None:
    global counter
    counter += 1
    if counter & ((1 << 14) - 1) == 0:
        # Check if counter is divisible by 2^14 efficiently and print status update
        print(f'Finished processing {counter} articles.')
    # Separate header from text with a newline.
    text = clean(text)
    outfile.write(f'<<<{title}>>>\n')
    for line in compact(text, structure=False):
        outfile.write(f'{line}\n')


def process_data(file_type: str, input_shadow, output_sentences) -> None:
    global prefix
    page = []
    id_shadow = None
    in_text = False
    redirect = False
    for line in input_shadow:
        if file_type != 'xml':
            line = str(line.decode('utf-8'))
        tag_shadow = ''
        if '<' in line:
            m = TAGS.search(line)
            if m:
                tag_shadow = m.group(2)
        if tag_shadow == 'page':
            page = []
            redirect = False
        elif tag_shadow == 'id' and not id_shadow:
            id_shadow = m.group(3)
        elif tag_shadow == 'title':
            title = m.group(3)
        elif tag_shadow == 'redirect':
            redirect = True
        elif tag_shadow == 'text':
            in_text = True
            line = line[m.start(3):m.end(3)] + '\n'
            page.append(line)
            if m.lastindex == 4:  # open-close
                in_text = False
        elif tag_shadow == '/text':
            if m.group(1):
                page.append(m.group(1) + '\n')
            in_text = False
        elif in_text:
            page.append(line)
        elif tag_shadow == '/page':
            colon = title.find(':')
            if colon < 0 and not redirect:
                wiki_document_sentences(output_sentences, title, ''.join(page))
            id_shadow = None
            page = []
        elif tag_shadow == 'base':
            # discover prefix from the xml dump file
            # /mediawiki/siteinfo/base
            base = m.group(3)
            prefix = base[:base.rfind('/')]


def init() -> None:
    global discard_element_patterns, ignored_tags, ignored_tag_patterns, self_closing_tag_patterns, \
        placeholder_tag_patterns

    for tag in discard_elements:
        pattern = re.compile(r'<\s*%s\b[^>]*>.*?<\s*/\s*%s>' % (tag, tag), re.DOTALL | re.IGNORECASE)
        discard_element_patterns.append(pattern)

    def ignore_tag(tag_shadow):
        left = re.compile(r'<\s*%s\b[^>]*>' % tag_shadow, re.IGNORECASE)
        right = re.compile(r'<\s*/\s*%s>' % tag_shadow, re.IGNORECASE)
        ignored_tag_patterns.append((left, right))

    for tag in ignored_tags:
        ignore_tag(tag)

    for tag in self_closing_tags:
        pattern = re.compile(r'<\s*%s\b[^/]*/\s*>' % tag, re.DOTALL | re.IGNORECASE)
        self_closing_tag_patterns.append(pattern)

    for tag, repl in list(placeholder_tags.items()):
        pattern = re.compile(r'<\s*%s(\s*| [^>]+?)>.*?<\s*/\s*%s\s*>' % (tag, tag), re.DOTALL | re.IGNORECASE)
        placeholder_tag_patterns.append((pattern, repl))


def main() -> None:
    parser = ArgumentParser(description='WikiExtractor', formatter_class=ArgumentDefaultsHelpFormatter)
    parser.add_argument('-i', '--infile', type=str,
                        help='Path to the Wikipedia dump file (uncompressed or bzip2).')
    parser.add_argument('-o', '--outfile', type=str, default='wiki.txt',
                        help='Output filename to save extracted Wikipedia dump text.')
    parser.add_argument('-d', '--dir', type=str, default='data',
                        help='Change default data directory relative to this script.')
    args = parser.parse_args()

    init()

    infile_path = path.join(args.dir, args.infile)
    outfile_path = path.join(args.dir, args.outfile)
    if 'bzip2' in guess_type(args.infile):
        with open(outfile_path, 'w') as outfile:
            process_data('bzip2', BZ2File(infile_path), outfile)
    else:
        with open(infile_path) as infile:
            with open(outfile_path, 'w') as outfile:
                process_data('xml', infile, outfile)


if __name__ == '__main__':
    main()
