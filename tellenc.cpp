// vim: expandtab shiftwidth=4 softtabstop=4 tabstop=4

/*
 * Copyright (C) 2006-2007 Wu Yongwei <wuyongwei@gmail.com>
 *
 * This software is provided 'as-is', without any express or implied
 * warranty.  In no event will the authors be held liable for any
 * damages arising from the use of this software.
 *
 * Permission is granted to anyone to use this software for any purpose,
 * including commercial applications, and to alter it and redistribute
 * it freely, subject to the following restrictions:
 *
 * 1. The origin of this software must not be misrepresented; you must
 *    not claim that you wrote the original software.  If you use this
 *    software in a product, an acknowledgement in the product
 *    documentation would be appreciated but is not required.
 * 2. Altered source versions must be plainly marked as such, and must
 *    not be misrepresented as being the original software.
 * 3. This notice may not be removed or altered from any source
 *    distribution.
 *
 */

//
// I use the following command line to build the executable on Windows with
// MSVC 6 + STLport 4.5.1:
//
//  CL /Ox /GX /Gr /G6 /MD /D_STLP_NO_IOSTREAMS tellenc.cpp /link /opt:nowin98
//

/**
 * @file    tellenc.cpp
 *
 * Program to guess the encoding of text.  It currently supports ASCII,
 * Latin1, UTF-8, GB2312, GBK, Big5, and any Unicode encodings with BOM.
 *
 * @version 1.2, 2007/02/23
 * @author  Wu Yongwei
 */

#include <algorithm>        // sort
#include <functional>       // binary_function
#include <map>              // map
#include <memory>           // pair
#include <vector>           // vector
#include <ctype.h>          // isprint
#include <errno.h>          // errno
#include <stdio.h>          // fopen/fclose/fprintf/printf/puts
#include <stdlib.h>         // exit
#include <string.h>         // memcmp/strcmp/strerror

#ifndef TELLENC_BUFFER_SIZE
#define TELLENC_BUFFER_SIZE 100000
#endif

using namespace std;

typedef unsigned short uint16_t;
typedef unsigned int uint32_t;
typedef pair<uint16_t, size_t> char_count_t;

struct freq_analysis_data_t {
    uint16_t    dbyte;
    const char* enc;
};

struct greater_char_count :
        public binary_function<const char_count_t&,
                               const char_count_t&,
                               bool> {
    result_type operator()(first_argument_type lhs, second_argument_type rhs)
    {
        if (lhs.second > rhs.second) {
            return true;
        }
        return false;
    }
};

enum UTF8_State {
    UTF8_INVALID,
    UTF8_1,
    UTF8_2,
    UTF8_3,
    UTF8_4,
    UTF8_TAIL
};

static const size_t MAX_CHAR = 256;
static const unsigned char NON_TEXT_CHARS[] = { 0, 26, 127, 255 };
static const char NUL = '\0';
static const int ODD = 1;
static const int EVEN = 2;

static UTF8_State utf8_char_table[MAX_CHAR];

static freq_analysis_data_t freq_analysis_data[] = {
    { 0xa3ac, "gbk" },
    { 0xa1a3, "gbk" },
    { 0xa1a1, "gbk" },
    { 0xa1ad, "gbk" },
    { 0xb5c4, "gbk" },
    { 0xbfc9, "gbk" },
    { 0xbaf3, "gbk" },
    { 0xd2bb, "gbk" },
    { 0xced2, "gbk" },
    { 0xcac7, "gbk" },
    { 0xb8f6, "gbk" },
    { 0xb2bb, "gbk" },
    { 0xc8cb, "gbk" },
    { 0xd5e2, "gbk" },
    { 0xc1cb, "gbk" },
    { 0xd6ae, "gbk" },
    { 0xa141, "big5" },
    { 0xa143, "big5" },
    { 0xaaba, "big5" },
    { 0xa7da, "big5" },
    { 0xa54c, "big5" },
    { 0xa66f, "big5" },
    { 0xa4a3, "big5" },
    { 0xa440, "big5" },
    { 0xa446, "big5" },
    { 0xa457, "big5" },
    { 0xbba1, "big5" },
    { 0xac4f, "big5" },
    { 0xa662, "big5" }
};

static bool is_binary = false;
static bool is_utf8_conformant = true;

static int nul_stat = 0;

bool verbose = false;

static inline bool is_non_text(char ch)
{
    for (size_t i = 0; i < sizeof(NON_TEXT_CHARS); ++i) {
        if (ch == NON_TEXT_CHARS[i]) {
            return true;
        }
    }
    return false;
}

static inline int is_odd_even(size_t pos)
{
    pos &= 1;
    if (pos) {
        return ODD;
    } else {
        return EVEN;
    }
}

void usage()
{
    fprintf(stderr, "Usage: tellenc [-v] <filename> \n");
    exit(EXIT_FAILURE);
}

void init_utf8_char_table()
{
    int ch = 0;
    utf8_char_table[ch] = UTF8_INVALID;
    ++ch;
    for (; ch <= 0x7F; ++ch) {
        utf8_char_table[ch] = UTF8_1;
    }
    for (; ch <= 0xBF; ++ch) {
        utf8_char_table[ch] = UTF8_TAIL;
    }
    for (; ch <= 0xC1; ++ch) {
        utf8_char_table[ch] = UTF8_INVALID;
    }
    for (; ch <= 0xDF; ++ch) {
        utf8_char_table[ch] = UTF8_2;
    }
    for (; ch <= 0xEF; ++ch) {
        utf8_char_table[ch] = UTF8_3;
    }
    for (; ch <= 0xF4; ++ch) {
        utf8_char_table[ch] = UTF8_4;
    }
    for (; ch <= 0xFF; ++ch) {
        utf8_char_table[ch] = UTF8_INVALID;
    }
}

static void init_char_count(char_count_t char_cnt[])
{
    for (size_t i = 0; i < MAX_CHAR; ++i) {
        char_cnt[i].first = i;
        char_cnt[i].second = 0;
    }
}

static void print_char_cnt(const char_count_t char_cnt[])
{
    for (size_t i = 0; i < MAX_CHAR; ++i) {
        unsigned char ch = (unsigned char)char_cnt[i].first;
        if (char_cnt[i].second == 0)
            break;
        printf("%.2x ('%c'): %-6u    ", ch,
               isprint(ch) ? ch : '?', char_cnt[i].second);
    }
    printf("\n");
}

static void print_dbyte_char_cnt(const vector<char_count_t>& dbyte_char_cnt)
{
    for (vector<char_count_t>::const_iterator it = dbyte_char_cnt.begin();
            it != dbyte_char_cnt.end(); ++it) {
        printf("%.4x: %-6u        ", it->first, it->second);
    }
}

static const char* check_ucs_bom(const unsigned char* const buffer)
{
    const struct {
        const char* name;
        const char* pattern;
        size_t pattern_len;
    } patterns[] = {
        { "ucs-4",      "\x00\x00\xFE\xFF",     4 },
        { "ucs-4le",    "\xFF\xFE\x00\x00",     4 },
        { "utf-8",      "\xEF\xBB\xBF",         3 },
        { "utf-16",     "\xFE\xFF",             2 },
        { "utf-16le",   "\xFF\xFE",             2 },
        { NULL,         NULL,                   0 }
    };
    for (size_t i = 0; patterns[i].name; ++i) {
        if (memcmp(buffer, patterns[i].pattern, patterns[i].pattern_len)
                == 0) {
            return patterns[i].name;
        }
    }
    return NULL;
}

static const char* check_dbyte(uint16_t dbyte)
{
    for (size_t i = 0;
            i < sizeof freq_analysis_data / sizeof(freq_analysis_data_t);
            ++i) {
        if (dbyte == freq_analysis_data[i].dbyte) {
            return freq_analysis_data[i].enc;
        }
    }
    return NULL;
}

const char* check_freq_dbytes(const vector<char_count_t>& dbyte_char_cnt)
{
    size_t max_comp_idx = 10;
    if (max_comp_idx > dbyte_char_cnt.size()) {
        max_comp_idx = dbyte_char_cnt.size();
    }
    for (size_t i = 0; i < max_comp_idx; ++i) {
        if (const char* enc = check_dbyte(dbyte_char_cnt[i].first)) {
            return enc;
        }
    }
    return NULL;
}

const char* tellenc(const unsigned char* const buffer, const size_t len)
{
    char_count_t char_cnt[MAX_CHAR];
    map<uint16_t, size_t> mp_dbyte_char_cnt;
    size_t dbyte_cnt = 0;
    size_t dbyte_hihi_cnt = 0;

    if (len > 4) {
        const char* result = check_ucs_bom(buffer);
        if (result) {
            return result;
        }
    }

    init_char_count(char_cnt);

    const unsigned char* p = buffer;
    unsigned char ch;
    int last_ch = EOF;
    int utf8_state = UTF8_1;
    while (p < buffer + len) {
        ch = *p;
        if (is_non_text(ch)) {
            if (!is_binary) {
                is_binary = true;
            }
            if (ch == NUL) {
                nul_stat |= is_odd_even(p - buffer);
            }
        }
        if (is_utf8_conformant) {
            switch (utf8_char_table[ch]) {
            case UTF8_INVALID:
                is_utf8_conformant = false;
                break;
            case UTF8_1:
                if (utf8_state != UTF8_1) {
                    is_utf8_conformant = false;
                }
                break;
            case UTF8_2:
                if (utf8_state == UTF8_1) {
                    utf8_state = UTF8_2;
                } else {
                    is_utf8_conformant = false;
                }
                break;
            case UTF8_3:
                if (utf8_state == UTF8_1) {
                    utf8_state = UTF8_3;
                } else {
                    is_utf8_conformant = false;
                }
                break;
            case UTF8_4:
                if (utf8_state == UTF8_1) {
                    utf8_state = UTF8_4;
                } else {
                    is_utf8_conformant = false;
                }
                break;
            case UTF8_TAIL:
                if (utf8_state > UTF8_1) {
                    utf8_state--;
                } else {
                    is_utf8_conformant = false;
                }
                break;
            }
        }
        char_cnt[ch].second++;
        if (last_ch != EOF) {
            uint16_t dbyte_char = (last_ch << 8) + ch;
            mp_dbyte_char_cnt[dbyte_char]++;
            dbyte_cnt++;
            if (last_ch > 0xa0 && ch > 0xa0) {
                dbyte_hihi_cnt++;
            }
            last_ch = EOF;
        } else if (ch >= 0x80) {
            last_ch = ch;
        }
        p++;
    }

    sort(char_cnt, char_cnt + MAX_CHAR, greater_char_count());

    if (verbose) {
        print_char_cnt(char_cnt);
    }

    vector<char_count_t> dbyte_char_cnt;
    for (map<uint16_t, size_t>::iterator it = mp_dbyte_char_cnt.begin();
            it != mp_dbyte_char_cnt.end(); ++it) {
        dbyte_char_cnt.push_back(*it);
    }
    sort(dbyte_char_cnt.begin(),
         dbyte_char_cnt.end(),
         greater_char_count());

    if (verbose) {
        print_dbyte_char_cnt(dbyte_char_cnt);
        printf("\n");
        printf("%u characters\n", len);
        printf("%u double-byte characters\n", dbyte_cnt);
        printf("%u double-byte hi-hi characters\n", dbyte_hihi_cnt);
        printf("%u unique double-byte characters\n", dbyte_char_cnt.size());
    }

    if (!is_utf8_conformant && is_binary) {
        switch (nul_stat) {
        case ODD:
            return "utf-16le";
        case EVEN:
            return "utf-16";
        default:
            return "binary";
        }
    } else if (dbyte_cnt == 0) {
        return "ascii";
    } else if (is_utf8_conformant) {
        return "utf-8";
    } else if (dbyte_hihi_cnt * 100 / dbyte_cnt < 5) {
        return "latin1";
    } else if (dbyte_hihi_cnt == dbyte_cnt) {
        return "gb2312";
    } else if (const char* enc = check_freq_dbytes(dbyte_char_cnt)) {
        return enc;
    }
    return NULL;
}

int main(int argc, char* argv[])
{
    const char* filename;
    if (argc == 3 && strcmp(argv[1], "-v") == 0) {
        verbose = true;
    }
    if (argc != 2 && !verbose) {
        usage();
    }
    if (verbose) {
        filename = argv[2];
    } else {
        filename = argv[1];
    }

    FILE* fp = fopen(filename, "rb");
    if (fp == NULL) {
        fprintf(stderr, "Cannot open file `%s': %s \n",
                        filename, strerror(errno));
        exit(EXIT_FAILURE);
    }

    unsigned char buffer[TELLENC_BUFFER_SIZE];
    size_t len;
    len = fread(buffer, 1, sizeof buffer, fp);

    init_utf8_char_table();
    if (const char* enc = tellenc(buffer, len)) {
        puts(enc);
    } else {
        puts("unknown");
    }

    fclose(fp);
    return 0;
}
