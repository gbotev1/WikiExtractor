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
from argparse import ArgumentParser
from typing import TextIO

# For status updates
counter = 0

# This is obtained from the dump itself.
prefix = None

accepted_namespaces = {'w'}  # w: Internal links to the Wikipedia

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
placeholder_tags = {'math': '*****', 'code': 'codice'}

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
PARAMETRIZED_LINK = re.compile(r'\[\[.*?]]')
COMMENT = re.compile(r'<!--.*?-->', re.DOTALL)
TAGS = re.compile(r'(.*?)<(/?\w+)[^>]*>(?:([^<]*)(<.*?>)?)?')
TITLE = re.compile(r'[\s_]+')
TITLE_MATCH = re.compile(r'([^:]*):(\s*)(\S(?:.*))')
SECTION = re.compile(r'(==+)\s*(.*?)\s*\1')
CLEANUP_1 = re.compile(r' (,:\.\)]Â»)')
CLEANUP_2 = re.compile(r'(\[\(Â«) ')
CLEANUP_3 = re.compile(r'\n\W+?\n')
CLEANUP_4 = re.compile(r'__[A-Z]+__')
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

        ns = prefix_shadow.capitalize()
        if ns in accepted_namespaces:
            # If the prefix designates a known namespace, then it might be
            # followed by optional whitespace that should be removed to get
            # the canonical page name
            # (e.g., "Category:  Births" should become "Category:Births").
            title = ns + ":" + rest.capitalize()
        else:
            # No namespace, just capitalize first letter.
            # If the part before the colon is not a known namespace, then we must
            # not remove the space after the colon (if any), e.g.,
            # "3001: The_Final_Odyssey" != "3001:The_Final_Odyssey".
            # However, to get the canonical page name we must contract multiple
            # spaces into one, because
            # "3001:   The_Final_Odyssey" != "3001: The_Final_Odyssey".
            title = prefix_shadow.capitalize() + ":" + optional_whitespace + rest
    else:
        # No namespace, so just capitalize first letter
        title = title.capitalize()
    return title


# Removes HTML or XML character references and entities from a text string.
# @param text The HTML (or XML) source text.
# @return The plain text, as a Unicode string, if necessary.
def unescape(text: str) -> str:
    def fixup(m: re.Match) -> str:
        text_inner = m.group(0)
        code = m.group(1)
        if text_inner[1] == "#":
            # Character reference
            if text_inner[2] == "x":
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
    colon = link.find(':')
    if colon > 0 and link[:colon] not in accepted_namespaces:
        return ''
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
    # Drop all remaining ones
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

    text = text.replace('<<', 'Â«').replace('>>', 'Â»')

    # Drop preformatted: this can't be done before since it may remove tags
    text = PREFORMATTED.sub('', text)

    # Cleanup text
    text = text.replace('\t', ' ')
    text = SPACES.sub(' ', text)
    text = DOTS.sub('...', text)
    text = re.sub(CLEANUP_1, r'\1', text)
    text = re.sub(CLEANUP_2, r'\1', text)
    text = re.sub(CLEANUP_3, '\n', text)  # Lines with only punctuation
    text = text.replace(',,', ',').replace(',.', '.')
    text = CLEANUP_4.sub('', text)
    # Add other filters here
    return text


def compact(text: str, structure: bool = False) -> list[str]:
    """Deal with headers, lists, empty sections, residuals of tables."""
    page = []  # list of paragraph
    headers = {}  # Headers for unfilled sections
    empty_section = False  # empty sections are discarded

    for line in text.split('\n'):
        if not line:
            continue
        # Handle section titles
        m = SECTION.match(line)
        if m:
            title = m.group(2)
            lev = len(m.group(1))
            if structure:
                page.append("<h%d>%s</h%d>" % (lev, title, lev))
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
                page.append("<li>%s</li>" % line[1:])
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
            page.append(line)  # first line
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
        print(counter)
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
            if (colon < 0 or title[:colon] in accepted_namespaces) and not redirect:
                wiki_document_sentences(output_sentences, title, ''.join(page))
            id_shadow = None
            page = []
        elif tag_shadow == 'base':
            # discover prefix from the xml dump file
            # /mediawiki/siteinfo/base
            base = m.group(3)
            prefix = base[:base.rfind("/")]


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
    parser = ArgumentParser(description='WikiExtractor')
    parser.add_argument('-i', '--infile', type=str,
                        help='Path to the Wikipedia dump file (uncompressed or bzip2).')
    parser.add_argument('-o', '--outfile', type=str, default='wiki.txt',
                        help='Output filename to save extracted Wikipedia dump text.')
    parser.add_argument('-d', '--dir', type=str, default='data',
                        help='Change default data directory relative to this script.')
    args = parser.parse_args()

    init()

    if 'bzip2' in guess_type(args.infile):
        with open(path.join(args.dir, args.outfile), 'w') as outfile:
            process_data('bzip2', BZ2File(args.infile), outfile)
    else:
        with open(path.join(args.dir, args.infile)) as infile:
            with open(path.join(args.dir, args.outfile), 'w') as outfile:
                process_data('xml', infile, outfile)


if __name__ == '__main__':
    main()
