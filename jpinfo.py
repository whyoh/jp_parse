
#! /usr/bin/python
# -*- coding: utf-8 -*-

# japanese web/irc/maillist/bbs/rss etc spider
# indexes to order kanjis, words and phrases by popularity/usefulness
# integrates with entrophilia quizzes to:
#    a) find articles/paragraphs/pages consisting of learnt words/kanjis
#    b) order dictionary to drive learning of words
#    c) fine-tune order to encompass "all common usaes of a kanji" so we can pass tests
#    d) provide a clean, friendly reader interface.
#        i) pop-up furigana
#        ii) colour-coding for learnt/learning/new/unknown/kana
#        iii) options to override learnt/order
#        iv) faster interface to entrophilia quizzes via REST

# hopefully uses jmdict/edict from stardict-dic-ja package

# hmm.  stardict appears to be able to add the furigana and english pop-up facility to anything anyway!
# well, stardict is a great find and dead useful.  probably going to be most useful here for testing/comparison.
# sdcv appears to be a c++ command line client.  so perhaps there is an API in there somewhere!  guess what - doesn't compile.
# maybe come back to this as an alternative.  i suspect reading the XML will be simpler for now.

# use wget/curl for spider function?
# wget has recursive retrieval.  if i run a parallel task that watches ....

# i don't really want to search randomly.  i want to scan wikipedia and then add feeds and new headline pages as i find good ones.
# if i'm not getting useful stats from the index ... add more feeds or find another big one like wikipedia.

# python+mysql+unicode seems a bit nightmarish.  for now try to make a dictionary index in memory and use the XML dict and urlencoding for the urls.

# should we bother with frames and iframes?  shouldn't be too tricky.

# first assumption failed - looks like ja.wikipedia.org doesn't have _any_ external links!  still, it's got lots of text (which is what we're actually after) and external references.

# 2ch very quickly generates a massive index of orz.2ch.io
# j-wave has a lot of 404s but still finds plenty
# amazon.co.jp seems to have a lot of pages that appear to be mostly english linked to from very japanese pages.


import urllib.request, urllib.error, urllib.parse
import sys, traceback
import os
import time
import psycopg2 as py_db
import socket
from html.parser import HTMLParser
from urllib.parse import urljoin, urlparse, urlunparse
from optparse import OptionParser
from datetime import datetime, timedelta
import threading
import subprocess
#from jmdict import jmdict
sys.path.append("..")
#from cmdmsg import cmdmsg

class vctHTMLParser(HTMLParser):
    readings = {}
    intd = False
    inth = False
    row = 0
    column = 0
    atype = ""
    btype = [['past', 'neg_past', 'nonpast', 'neg', 'imp', 'te', 'vol'],
            ['pol_past', 'pol_negpast', 'pol_nonpast', 'pol_neg', 'pol_imp', 'pol_te', 'pol_vol'],
            ['tari', 'i', 'condra', 'condeba', 'pass', 'cause', 'pot']]

    def handle_starttag(self, tag, attrs):
        if tag == "td":
            self.intd = True
            if self.row > 0: self.column += 1
        if tag == "th" and len(attrs) == 1 and attrs[0][0] == "colspan" and attrs[0][1] == "7":
            self.inth = True
            self.row = 0
        if tag == "tr":
            self.row += 1
            self.column = 0

    def handle_endtag(self, tag):
        if tag == "td":
            self.intd = False
        if tag == "th":
            if self.atype != "" and self.atype not in self.readings: self.readings[self.atype] = {}
            if self.atype == "vs-i" and "vs" not in self.readings: self.readings["vs"] = {}
            self.inth = False

    def handle_data(self, data):
        udata = data
        if self.intd and self.row > 0 and self.column > 1 and self.atype != "" and data != "" and data != "-":
            if data == "| [root]": udata = u""
            if udata.find(u"(") >= 0 and udata.find(u")") >= 0:
                udata = udata[:udata.find(u"(")] + udata[udata.find(u")") + 1:] + u" + " + udata.replace(u"(", u"").replace(u")", u"")
            num = 1
            for udatum in udata.split(u" + "):
                udatum = udatum.strip().strip(u" /")
                datum = udatum.encode("utf-8")
                thistype = self.btype[self.row - 1][self.column - 2]
                if num > 1:
                    if self.atype == "vd" and self.row == 3: thistype = "pol_" + thistype
                    else: thistype += str(num)
                if self.atype == "vs-i": self.readings["vs"][thistype] = datum
                if self.atype == "vk":
                    self.readings[self.atype+"_k"][thistype] = datum
                    self.readings[self.atype][thistype] = (u"く" + udatum[1:]).encode("utf-8")
                else: self.readings[self.atype][thistype] = datum
                num += 1
        if self.inth:
            if data.find("Weak verbs") >= 0: self.atype = "v1"
            elif data.find("Strong verbs") >= 0:
                if udata.find(u"ぶ") >= 0: self.atype = "v5b"
                elif udata.find(u"ぐ") >= 0: self.atype = "v5g"
                elif udata.find(u"く") >= 0: self.atype = "v5k"
                elif udata.find(u"む") >= 0: self.atype = "v5m"
                elif udata.find(u"ぬ") >= 0: self.atype = "v5n"
                elif udata.find(u"す") >= 0: self.atype = "v5s"
                elif udata.find(u"つ") >= 0: self.atype = "v5t"
                elif udata.find(u"う") >= 0: self.atype = "v5u"
                elif udata.find(u"る") >= 0: self.atype = "v5r"
            elif data.find("する") >= 0: self.atype = "vs-i"
            elif data.find("くる") >= 0: self.atype = "vk"
            elif data.find("だ") >= 0: self.atype = "vd"
            else: self.atype = ""

class jaHTMLParser(HTMLParser):

    currenttext=u""
    # TODO should find the following in the HTML specs
    # try http://dev.w3.org/html5/spec/Overview.html#attributes-1
    # 13oct2011 ignore noscript - it's usually just "you need script".
    # and noframes for much the same reason
    blocktag = ['p','div', 'table', 'tbody', 'tr', 'td', 'body', 'title', 'h1', 'h2', 'h3', 'form', 'input', 'ul', 'li', 'ol', 'label', 'hr', 'br', 'iframe', 'script', 'blockquote', 'button', 'area', 'map', 'object', 'h4', 'dl', 'dt', 'dd', 'h5', 'h6', 'select', 'option', 'center', 'spacer', 'address', 'frameset', 'frame', 'textarea', 'th', 'code', 'pre', 'thead', 'tfoot', 'caption', 'layer', 'fieldset', 'xhtml', 'o:p', 'optgroup', 'applet', 'rdf:description', 'rdf:rdf', 'fn:distribution', 'fn:type', 'x-claris-window', 'x-claris-tagview', 'headline', 'nolayer', 'bpdy', 'xml', 'q', 'samp', 'kbd', 'quote', 'tabletable', 'noembed', 'rb', 'rp', 'rt', 'ruby', 'left', 'sub', 'del']
    ignoretag = ['head', 'html', 'meta', 'style', 'link', 'colgroup', 'comment', 'ajj_comment', 'lastmod', 'dis.n', 'noscript', 'noframes']
    unknowntag = ['param', 'embed', 'sup', 'nobr', 'tt', 'content', 'col', 'ins', 'marquee', 'im_bodey', 'im_page', 'wbr', 'base', 'basefont', 'ssinfo', 'fragmentinstance', 'region', 'element', 'classes', 'class', 'legend', 'metal:pan', 'csaction', 'csscriptdict', 'csactiondict', 'csobj', 'kanhanbypass', 'csactions']
    inlinetag = ['span', 'a', 'img', 'b', 'i', 'strong', 'em', 'style', 'font', 'small', 'u', 'big', 'abbr', 'number', 'cite', 'blink', 'acronym', 'kdb', 's', 'picture', 'mars:language', 'nowrap', 'insert', 'copy', 'strike', 'hyperlink', 'ilayer', 'en', 'var', 'defanged_link', 'dfn', 'o:smarttagtype', 'st1:place', 'st1:placename', 'st1:placetype', 'st1:state', 'm', 'l', 'fx']
    # linktags complete from html5 spec (plus 'frame') as of 13oct2011
    # probably want to ignore some of these .. not sure which or how/where yet
    linktag = {'href': ['a', 'area', 'link', 'base'], 'src': ['video', 'audio', 'frame', 'iframe', 'embed', 'img', 'input', 'script', 'source', 'track'], 'action': ['form'], 'cite': ['blockquote', 'del', 'ins', 'q'], 'data': ['object'], 'formaction': ['button', 'input'], 'icon': ['command'], 'manifest': ['html'], 'poster': ['video']}

    # 'block' tags used often without necessarily breaking a sentence.
    jointag=['br']

    unentities = {}

    jaentities = {
    'MA': "martial arts term",
    'X': "rude or X-rated term (not displayed in educational software)",
    'abbr': "abbreviation",
    'adj-i': "adjective (keiyoushi)",
    'adj-na': "adjectival nouns or quasi-adjectives (keiyodoshi)",
    'adj-no': "nouns which may take the genitive case particle `no'",
    'adj-pn': "pre-noun adjectival (rentaishi)",
    'adj-t': "`taru' adjective",
    'adj-f': "noun or verb acting prenominally",
    'adj': "former adjective classification (being removed)",
    'adv': "adverb (fukushi)",
    'adv-to': "adverb taking the `to' particle",
    'arch': "archaism",
    'ateji': "ateji (phonetic) reading",
    'aux': "auxiliary",
    'aux-v': "auxiliary verb",
    'aux-adj': "auxiliary adjective",
    'Buddh': "Buddhist term",
    'chn': "children's language",
    'col': "colloquialism",
    'comp': "computer terminology",
    'conj': "conjunction",
    'ctr': "counter",
    'derog': "derogatory",
    'eK': "exclusively kanji",
    'ek': "exclusively kana",
    'exp': "Expressions (phrases, clauses, etc.)",
    'fam': "familiar language",
    'fem': "female term or language",
    'food': "food term",
    'geom': "geometry term",
    'gikun': "gikun (meaning) reading",
    'hon': "honorific or respectful (sonkeigo) language",
    'hum': "humble (kenjougo) language",
    'iK': "word containing irregular kanji usage",
    'id': "idiomatic expression",
    'ik': "word containing irregular kana usage",
    'int': "interjection (kandoushi)",
    'io': "irregular okurigana usage",
    'iv': "irregular verb",
    'ling': "linguistics terminology",
    'm-sl': "manga slang",
    'male': "male term or language",
    'male-sl': "male slang",
    'math': "mathematics",
    'mil': "military",
    'n': "noun (common) (futsuumeishi)",
    'n-adv': "adverbial noun (fukushitekimeishi)",
    'n-suf': "noun, used as a suffix",
    'n-pref': "noun, used as a prefix",
    'n-t': "noun (temporal) (jisoumeishi)",
    'num': "numeric",
    'oK': "word containing out-dated kanji",
    'obs': "obsolete term",
    'obsc': "obscure term",
    'ok': "out-dated or obsolete kana usage",
    'poet': "poetical term",
    'pol': "polite (teineigo) language",
    'pref': "prefix",
    'prt': "particle",
    'physics': "physics terminology",
    'rare': "rare",
    'sens': "sensitive",
    'sl': "slang",
    'suf': "suffix",
    'uK': "word usually written using kanji alone",
    'uk': "word usually written using kana alone",
    'v1': "Ichidan verb",
    'v4r': "Yondan verb with `ru' ending (archaic)",
    'v5': "Godan verb (not completely classified)",
    'v5aru': "Godan verb - -aru special class",
    'v5b': "Godan verb with `bu' ending",
    'v5g': "Godan verb with `gu' ending",
    'v5k': "Godan verb with `ku' ending",
    'v5k-s': "Godan verb - Iku/Yuku special class",
    'v5m': "Godan verb with `mu' ending",
    'v5n': "Godan verb with `nu' ending",
    'v5r': "Godan verb with `ru' ending",
    'v5r-i': "Godan verb with `ru' ending (irregular verb)",
    'v5s': "Godan verb with `su' ending",
    'v5t': "Godan verb with `tsu' ending",
    'v5u': "Godan verb with `u' ending",
    'v5u-s': "Godan verb with `u' ending (special class)",
    'v5uru': "Godan verb - Uru old class verb (old form of Eru)",
    'v5z': "Godan verb with `zu' ending",
    'vz': "Ichidan verb - zuru verb (alternative form of -jiru verbs)",
    'vi': "intransitive verb",
    'vk': "Kuru verb - special class",
    'vn': "irregular nu verb",
    'vs': "noun or participle which takes the aux. verb suru",
    'vs-s': "suru verb - special class",
    'vs-i': "suru verb - irregular",
    'kyb': "Kyoto-ben",
    'osb': "Osaka-ben",
    'ksb': "Kansai-ben",
    'ktb': "Kantou-ben",
    'tsb': "Tosa-ben",
    'thb': "Touhoku-ben",
    'tsug': "Tsugaru-ben",
    'kyu': "Kyuushuu-ben",
    'rkb': "Ryuukyuu-ben",
    'vt': "transitive verb",
    'vulg': "vulgar expression or word"
    }
# from http://en.wikipedia.org/wiki/Japanese_verb_conjugations, http://en.wikibooks.org/wiki/Japanese/Verb_conjugation_table and http://www.guidetojapanese.org
    tenses = {'nonpast':'present/future', 'past':'past', 'condra':'if and when', 'condraba':'if and when - formal',
        'neg':'not', 'i':'for/formal', 'te':'and/command', 'pot':'able to do', 'cause':'cause or enable to do', 'condeba':'if able to',
        'imp':'an instruction', 'pass':'indirectly/regrettably', 'vol':'possibility', 'pos': "possesive", 'to': "to adverb",
        'negte': "don't", 'polv': "polite verb", 'tai': "expressing a wish", 'washinai': "strong negative intention",
        'nasai': "a command", 'na': "a command", 'yasui': "easy", 'nikui': "difficult", 'sugiru': "excessive",
        'yagaru': "disrespectful", 'ni': "purpose", 'n': "polite", 'kure': "request", 'kudasai': "request",
        'kudasaik': "request", 'teiru': "currently", 'teoku': "completed for later", 'tearu': "completed object",
        'teshimau': "unexpected", 'temiru': "attempt", 'teiku': "continuous or changing",
        'tekuru': "continuous or changed", 'waikenai': "must not", 'wadame': "must not", 'moii': "permitted to",
        'mokamawanai': "allowed/invited", 'hoshii': "requested", 'sumimasen': "sorry for doing",
        'neg_past': "negative past", 'pol_past': "past (polite)", 'pol_negpast': "negative past (polite)", 'pol_nonpast': "present/future (polite)",
        'pol_neg': "negative (polite)", 'pol_imp': "an instruction (polite)", 'pol_te': "(polite)", 'pol_vol': "possibility (polite)",
        'tari': "tari"}

    endings = {
    'vs': {'nonpast':'する', 'past':'した', 'neg':'しない', 'i':'し', 'te':'して', 'pot':'できる', 'pot2':'せる',
        'cause':'させる', 'condeba':'すれば', 'imp':'しろ', 'imp2':'せよ', 'pass':'される', 'vol':'しよう', 'vol2':'せよう'},
    'v5u': {'past':'った', 'neg':'わない', 'i':'い', 'te':'って', 'pot':'える', 'cause':'わせる', 'condeba':'えば', 'imp':'え', 'pass':'われる', 'vol':'おう'},
    'v5k': {'past':'いた', 'neg':'かない', 'i':'き', 'te':'いて', 'pot':'ける', 'cause':'かせる', 'condeba':'けば', 'imp':'け', 'pass':'かれる', 'vol':'こう'},
    'v5g': {'past':'いだ', 'neg':'がない', 'i':'ぎ', 'te':'いで', 'pot':'げる', 'cause':'がせる', 'condeba':'げば', 'imp':'げ', 'pass':'がれる', 'vol':'ごう'},
    'v5s': {'past':'した', 'neg':'さない', 'i':'し', 'te':'して', 'pot':'せる', 'cause':'させる', 'condeba':'せば', 'imp':'せ', 'pass':'される', 'vol':'そう'},
    'v5t': {'past':'った', 'neg':'たない', 'i':'ち', 'te':'って', 'pot':'てる', 'cause':'たせる', 'condeba':'てば', 'imp':'て', 'pass':'たれる', 'vol':'とう'},
    'v5n': {'past':'んだ', 'neg':'なない', 'i':'に', 'te':'んで', 'pot':'ねる', 'cause':'なせる', 'condeba':'ねば', 'imp':'ね', 'pass':'なれる', 'vol':'のう'},
    'v5b': {'past':'んだ', 'neg':'ばない', 'i':'び', 'te':'んで', 'pot':'べる', 'cause':'ばせる', 'condeba':'べば', 'imp':'べ', 'pass':'ばれる', 'vol':'ぼう'},
    'v5m': {'past':'んだ', 'neg':'まない', 'i':'み', 'te':'んで', 'pot':'める', 'cause':'ませる', 'condeba':'めば', 'imp':'め', 'pass':'まれる', 'vol':'もう'},
    'v5r': {'past':'った', 'neg':'らない', 'i':'り', 'te':'って', 'pot':'れる', 'cause':'らせる', 'condeba':'れば', 'imp':'れ', 'pass':'られる', 'vol':'ろう'},
    'adj-i': {'past':'かった', 'neg':'くない', 'te':'くて', 'cause':'くさせる', 'condeba':'ければ'},
    'adj-na': {'past':'だった', 'neg':'ではない', 'neg2':'じゃない', 'te':'で', 'cause':'にさせる', 'condeba':'であれば'},
    'adj-no': {'pos': "の"},
    'adv-to': {'to': "と"},
    'eK': {},
    'ek': {},
    'n-suf': {},
    'n-pref': {},
    'pref': {},
    'suf': {},
    'uK': {},
    'uk': {},
    'v1': {'past':'た', 'neg':'ない', 'i':'', 'te':'て', 'pot':'られる', 'pot2':'れる',
        'cause':'させる', 'condeba':'れば', 'imp':'ろ', 'imp2':'よ', 'pass':'られる', 'vol':'よう'},
    'v5k-s': {'nonpast':'いく', 'past':'いった', 'te':'いって'},
    'v5r-i': {'neg':'ない'},
    'v5aru': {},
    'vn': {},
    'vs-s': {},
    'vs-i': {'nonpast':'する', 'past':'した', 'neg':'しない', 'i':'し', 'te':'して', 'pot':'できる', 'pot2':'せる',
        'cause':'させる', 'condeba':'すれば', 'imp':'しろ', 'imp2':'せよ', 'pass':'される', 'vol':'しよう', 'vol2':'せよう'},
    'n': {'nonpast': "ます", 'past': "ました", 'neg': "ません", 'te': "まして", 'imp': "ませ", 'vol': "ましょう"}, # -masu endings
    'condra': {'condraba': "ば"},
    'past': {'condra': 'ら'},
    'nai': {'negte': "いで", 'condeba': "ければ"}, # special for neg te - "don't do this"
    'i': {'n': "", 'tai': "たい", 'washinai': "はしない", 'nasai': "なさい", 'na': "な", 'yasui': "やすい", 'nikui': "にくい", 'sugiru': "すぎる", 'yagaru': "やがる", 'ni': "に"},
    'te': {'kure': "くれ", 'kudasai': "ください", 'kudasai_k': "下さい", 'teiru': "いる", 'teoku': "おく", 'tearu': "ある",
        'teshimau': "しまう", 'temiru': "みる", 'teiku': "いく", 'tekuru': "くる", 'waikenai': "はいけない", 'wadame': "はだめ",
        'moii': "もいい", 'mokamawanai': "もかまわない", 'hoshii': "ほしい", 'hoshii_k': "欲しい", 'sumimasen': "すみません"},
    'nul': {'dict': ""}
    }

    def __init__(self, db_cursor):
        HTMLParser.__init__(self)
        # TODO: read in entities from specified DTD.  maybe do that outside and pass as an option
        for k,v in self.jaentities.items(): self.unentities[v] = k
        self.db_cursor = db_cursor

    def iscjk(self, string):
        paraja = 0
        for c in string:
            u8 = c.encode("utf-8")
            if u8 == u"\u00d7".encode("utf-8"): paraja += 1
            elif u8 >= u"\u0370".encode("utf-8") and u8 <= u"\u03ff".encode("utf-8"): paraja += 1
            elif u8 >= u"\u2000".encode("utf-8") and u8 <= u"\u206f".encode("utf-8"): paraja += 1
            elif u8 >= u"\u2190".encode("utf-8") and u8 <= u"\u22ff".encode("utf-8"): paraja += 1
            elif u8 >= u"\u25a0".encode("utf-8") and u8 <= u"\u25ff".encode("utf-8"): paraja += 1
            elif u8 >= u"\u3000".encode("utf-8") and u8 <= u"\u30ff".encode("utf-8"): paraja += 1
            elif u8 >= u"\u4e00".encode("utf-8") and u8 <= u"\u9fff".encode("utf-8"): paraja += 1
            elif u8 >= u"\uff00".encode("utf-8") and u8 <= u"\uffef".encode("utf-8"): paraja += 1
        return paraja

    def isreading(self, string):
        paraja = 0
        for c in string:
            u8 = c.encode("utf-8")
            if u8 >= u"\u2200".encode("utf-8") and u8 <= u"\u22ff".encode("utf-8"): paraja += 1
            elif u8 >= u"\u3000".encode("utf-8") and u8 <= u"\u303f".encode("utf-8"): paraja += 1
            elif u8 >= u"\u3040".encode("utf-8") and u8 <= u"\u309f".encode("utf-8"): paraja += 1
            elif u8 >= u"\u30a0".encode("utf-8") and u8 <= u"\u30ff".encode("utf-8"): paraja += 1
            elif u8 >= u"\uff00".encode("utf-8") and u8 <= u"\uffef".encode("utf-8"): paraja += 1
        return paraja

    # strlen is the length of string which matches kanji/reading or skanji/sreading
    # word is the current form of the string - not necessarily matching string[:strlen]
    def doending(self, wtype, string, conjs, word, reading):
        #print "TRACE1:", wtype, string.encode("utf-8"), conjs, word.encode("utf-8"), reading.encode("utf-8")
        composite = {"pass": ["v1"], "cause": ["v1"], "pot": ["v1"], "neg": ["adj-i", "nai"],
            "i": ["i"], "n":["n"], "tai": ["adj-i"], "washinai": ["adj-i"], "yasui": ["adj-i"], "nikui": ["adj-i"], "sugiru": ["v5r"], "yagaru": ["v5r"],
            "te": ["te"], 'teiru': ["v1"], 'teoku': ["v5k"], 'tearu': ["v5r-i"], 'teshimau': ["v5u"], 'temiru': ["v1"], 'teiku': ["v5k"], 'tekuru': ["vk"],
            "pol_te": ["te"]}
        appenders = ["condra", "past", "i", "adj-na","adj-no","adv-to","n","vz","vs","vs-s", "te"]
        doublers = ["vs-i", "vk"]
        if wtype in appenders:
            wordroot = word
            readroot = reading
        elif wtype in doublers:
            wordroot = word[:-2]
            readroot = reading[:-2]
        else:
            wordroot = word[:-1]
            readroot = reading[:-1]
        rconjs = []
        bestword = ""
        bestreading = ""
        besttenses = []
        if wtype not in self.endings: return bestword, bestreading, besttenses
        for v in conjs:
            if v[-1:] == '2': v = v[:-1]
            elif v[:-2] == "_k": v = v[:-2]
            elif v[:4] == "pol_": v = v[4:]
            if v not in rconjs: rconjs.append(v)
        for tense, ending in self.endings[wtype].iteritems():
            ending = ending.decode('utf-8')
            if tense[-1:] == '2': rtense = tense[:-1]
            elif tense[:-2] == "_k": rtense = tense[:-2]
            elif tense[:4] == "pol_": rtense = tense[4:]
            else: rtense = tense
            if rtense in rconjs: continue
            thistenses = conjs+[tense]
            newword = wordroot+ending
            if len(newword) > len(string) + 1: continue
            if tense[-2:] == "_k": newreading = readroot+self.endings[wtype][tense[:-2]].decode('utf-8')
            else: newreading = readroot+ending
            if string[:len(newword) - 1] != newword[:len(newword) - 1]: continue
            if string[:len(newword)] == newword and len(newword) > len(bestword):
                    bestword = newword
                    bestreading = newreading
                    besttenses = thistenses[:]
            # see if it can be extended further
            # following are rules for making one ending out of another, rather than a composite tense out of both.
            if rtense in ["condra", "past"]:
                thisword, thisreading, thistenses = self.doending(rtense, string, conjs, newword, newreading)
                if string[:len(thisword)] == thisword and len(thisword) > len(bestword):
                    bestword = thisword
                    bestreading = thisreading
                    besttenses = thistenses[:]
            # whereas these are composite tenses
            if rtense in composite:
                for newtense in composite[rtense]:
                    thisword, thisreading, thistenses = self.doending(newtense, string, conjs+[tense], newword, newreading)
                    if string[:len(thisword)] == thisword and len(thisword) > len(bestword):
                        bestword = thisword
                        bestreading = thisreading
                        besttenses = thistenses[:]
        if len(bestword) and len(besttenses) == 0:
            print("lack of conjugations weirdness!")
            sys.exit(1)
        if len(bestword) and bestword != string[:len(bestword)]:
            print("assert thingy - unmatching weirdness!", bestword, "doesn't match", string[:len(bestword)], "in", string, repr(besttenses), wtype)
            sys.exit(1)
        #print "TRACE3:", bestword.encode("utf-8"), bestreading.encode("utf-8"), besttenses
        return bestword, bestreading, besttenses

    def lookup(self, string, suffix, kr):
        #if suffix: where = "substr(%s, 1, char_length(%s) - %d)" % (kr, kr, suffix)
        if suffix == 2: where = "ss" + kr
        elif suffix == 1: where = "s" + kr
        else: where = kr
        self.db_cursor.execute(
            "select jmdictID,senseID, tense, type, %s,reading from USERDATA.`{}` where %s='%s' order by score".format(self.dicttable),
            (kr, where, string))
        return self.db_cursor

    def getamatch4(self, string):
        atype = None
        row = None
        if not self.iscjk(string[0]): return 0, None, None
        # TODO: when multi-threaded we should requery self.biggest?
            # or possibly just miss it out.
        debug = False
        #if string[:2] == u"です": debug = True

        strlen = min(
            self.biggest, len(string),
            len(string.partition(u'、')[0]), len(string.partition(u'。')[0]), len(string.partition(u'・')[0]),
            len(string.partition(u'）')[0]), len(string.partition(u'（')[0]), len(string.partition(u'」')[0]), len(string.partition(u'「')[0]),
            len(string.partition(u'(')[0]), len(string.partition(u'『')[0]), len(string.partition(u'』')[0]), len(string.partition(u')')[0]),
            len(string.partition(u'：')[0]), len(string.partition(u':')[0]), len(string.partition(u' ')[0]), len(string.partition(u'“')[0]),
            len(string.partition(u'，')[0]), len(string.partition(u']')[0]), len(string.partition(u'[')[0]), len(string.partition(u'”')[0]),
            len(string.partition(u'､')[0]), len(string.partition(u'!')[0]), len(string.partition(u'?')[0]))

        beststrlen = 0
        bestatype = None
        bestestrow = None
        bestinsert = None
        bestinsert_params = None
        # deal with the most irregular verb as a one-off special case - "to be"
        for tobetype, tobeending in self.endings['vd'].iteritems():
            utobe = tobeending.decode('utf-8')
            if string[:strlen] == utobe:
                if string[:2] == u"じゃ": bestestrow = [["1005900", "5", "vd-"+tobetype, "auxiliary"]]
                elif string[:1] == u"で": bestestrow = [["1628500", "0", "vd-"+tobetype, "auxiliary"]]
                elif string[:1] == u"だ": bestestrow = [["2089020", "0", "vd-"+tobetype, "auxiliary"]]
                else: continue
                # nara has a dict entry of its own. .. or that might be something else
                beststrlen = strlen
                bestatype = "reading"
                bestesttenses = ["vd", tobetype]
                bestinsert = "reading='%s', sreading='%s', ssreading='%s', type='%s', kanji='%s', skanji='%s', sskanji='%s'"
                bestinsert_params = (utobe, utobe[:-1], utobe[:-2], "auxiliary", utobe, utobe[:-1], utobe[:-2])
                bestestlen = len(tobeending)
        # if it's not "to be"
        if not bestestrow:
        # for each decreasing substring
            while strlen:
                bestword = ""
                bestreading = ""
                bestrow = []
                besttenses = None
                bestsuffix = 0
                if self.isreading(string[:strlen]) < strlen: atype = "kanji"
                else: atype = "reading"
                allrows = []
                exact = False
                # find an exact match
                res = self.lookup(string[:strlen], 0, atype)
                row = res.fetchone()
                while row:
                    exact = True
                    allrows.append(row[:])
                    #if debug: print "exact", row[0][2], row[0][3], row[0][4], row[0][5]
                    row = res.fetchone()
                if exact:
                    bestrow = allrows[-1][:]
                    bestword = bestrow[0][4].decode('utf-8')
                # if there's enough text then look for a partial match
                if strlen > 1:
                    res = self.lookup(string[:strlen - 1], 1, atype)
                    row = res.fetchone()
                    while row:
                        allrows.append(row[:])
                        #if debug: print "approx", row[0][2], row[0][3], row[0][4], row[0][5]
                        row = res.fetchone()
                if strlen > 2:
                    res = self.lookup(string[:strlen - 2], 2, atype)
                    row = res.fetchone()
                    while row:
                        allrows.append(row[:])
                        #if debug: print "approx", row[0][2], row[0][3], row[0][4], row[0][5]
                        row = res.fetchone()
                # attempt to conjugate each one
                for row in allrows:
                    thesetenses = row[0][2].split("-")
                    conjlen = 0
                    if row[0][2] == "dict":
                        wtypes = []
                        for btype in row[0][3].split(';'): wtypes.append(self.unentities[btype.strip()])
                    else: wtypes = thesetenses[-1:]
                    for wtype in wtypes:
                        if row[0][2] == "dict": thesetenses = [wtype.replace("-", "_")]
                        thisword, thisreading, thistenses = self.doending(wtype, string, thesetenses, row[0][4].decode('utf-8'), row[0][5].decode('utf-8'))
                        # remember the best conjugated result
                        if len(thisword) > len(bestword):
                            bestword = thisword
                            bestreading = thisreading
                            besttenses = thistenses
                            bestrow = row[:]
                row = bestrow[:]
                # if there was an exact match or a better conjugation and it was the best so far
    #                if len(bestword) and (len(bestword) > beststrlen or (len(bestword) == beststrlen and not exact)):
                if debug and len(bestword): print(beststrlen, strlen, bestword.encode('utf-8'))
                if len(bestword) and (len(bestword) >= beststrlen):
                    # if conjugated
                    if besttenses:
                        if debug: print("dealing with conjugation")
                        # figure out the kanji and reading versions from the dict form
                        cursor.execute("select reading, kanji, meaning from USERDATA.`" + self.dicttable + "` where jmdictID=%s and senseID=%s and tense='%s'" % (row[0][0], row[0][1], row[0][2]))
                        row2 = cursor.fetchone()[0]
                        if bestword == bestreading and row2[0] != row2[1]:
                            # the original is non-kanji but there's a kanji version in the dictionary
                            # so derive a new bestword
                            rword = row2[0].decode('utf-8')
                            kword = row2[1].decode('utf-8')
                            suffixpos = 0
                            while suffixpos < len(rword) and suffixpos < len(bestword) and rword[suffixpos] == bestword[suffixpos]: suffixpos += 1
                            suffixlen = suffixpos - len(rword)
                            if suffixlen == 0: prefix = kword
                            else: prefix = kword[:suffixlen]
                            newsuffixlen = suffixpos - len(bestword)
                            if newsuffixlen == 0: suffix = ""
                            else: suffix = bestword[newsuffixlen:]
                            bestword = prefix+suffix
                        # we might have changed bestword to the kanji by now so check reading too
                        if bestword != string[:len(bestword)] and bestreading != string[:len(bestreading)]:
                            print(string + " (" + bestword + " from " + row[0][4] + ") doesn't match " + bestword + " or " + bestreading + " : " + row2[2])
                            sys.exit(1)
                        # we'll always pick up the non-exact conjugation before the existing exact match
                        #elif len(bestword) > beststrlen:
                        #    print "already got", bestword.encode('utf-8'), "or", bestreading.encode('utf-8'), "from", string.encode('utf-8')
                        #    sys.exit(1)
                        row = [[row[0][0], row[0][1], "-".join(besttenses), row[0][3]]]
                        if self.isreading(string[:len(bestword)]) < len(string[:len(bestword)]): atype = "kanji"
                        else: atype = "reading"
                        if len(bestword) >= beststrlen:
                            beststrlen = len(bestword)
                            bestatype = atype
                            bestestrow = row[:]
                            if debug: print("conjugated", row[0][2], row[0][3])
                            bestesttenses = besttenses[:]
                            bestinsert = "reading='%s', sreading='%s', ssreading='%s', type='%s', kanji='%s', skanji='%s', sskanji='%s'"
                            bestinsert_params = (bestreading, bestreading[:-1], bestreading[:-2], row[0][3], bestword, bestword[:-1], bestword[:-2])
                            bestestlen = max(len(bestreading), len(bestword))
                    # if it wasn't conjugated then it must be an exact match
                    else:
                        beststrlen = strlen
                        bestatype = atype
                        bestestrow = row[:]
                        if debug: print("exact", row[0][2], row[0][3])
                        bestinsert = None
                strlen -= 1 # try a shorter string
        #if strlen < 3 and len(string) >= 3 and string[1:3] == u"され" and not self.isreading(string): sys.exit(1)
        if beststrlen and bestinsert:
            row = bestestrow[:]
            # TODO: lock tables
            cursor.execute("select count(*) from USERDATA.`%s` where jmdictID=%s and senseID=%s and tense='%s'" % (self.dicttable, row[0][0], row[0][1], row[0][2]))
            if int(cursor.fetchone()[0][0]) == 0:
                #cursor.execute("select max(ID/100000000000) from USERDATA.`" + self.dicttable + "` where jmdictID=%s and senseID=%s" % (row[0][0], row[0][1]))
                #maxtense = int(float(cursor.fetchone()[0][0])) + 1
                cursor.execute("select meaning from USERDATA.`" + self.dicttable + "` where jmdictID=%s and senseID=%s and tense='dict'" % (row[0][0], row[0][1]))
                dictmeaning = cursor.fetchone()[0][0]
                longtense = []
                numtenses = len(bestesttenses)
                tenseno = 1
                for tense in bestesttenses[1:]:
                    if tense[-1:] == "2": rtense = tense[:-1]
                    elif tense[-2:] == "_k": rtense = tense[:-2]
                    else: rtense = tense
                    tenseno += 1
                    if rtense in ["te", "i"] and tenseno < numtenses: continue
                    longtense.append(self.tenses[rtense])
                # FIXME: if we haven't narrowed it down then add for each dict with same atype
                params = [self.dicttable, row[0][0]] + list(bestinsert_params) + [dictmeaning+" ("+ ", ".join(longtense) + ")", row[0][1], row[0][0]+row[0][1]+row[0][2], row[0][2]]
                cursor.execute(
                    "insert into USERDATA.`%s` set jmdictID=%s, %s, meaning='%s', senseID=%s, ID=conv(substring(sha1('%s'), 1, 15), 16, 10), tense='%s'", params)
                if bestestlen > self.biggest: self.biggest = bestestlen
        if string[:2] == u"です" and beststrlen == 1:
            print("desu error!!!")
            sys.exit(1)
        return beststrlen, bestatype, bestestrow

    def process_text(self):
        paraja = 0
        paranonja = 0
        order = 0
        self.currenttext = self.currenttext.strip()
        self.currenttext = self.currenttext.replace(u"\n", u" ")
        self.currenttext = self.currenttext.replace(u"\t", u" ")
        while self.currenttext.find(u"  ") > -1: self.currenttext = self.currenttext.replace(u"  ", u" ")
        janonja = ""
    # check symbols
    # uses ranges scanned from jmdict using checkdict.py
        for c in self.currenttext:
            u8 = c.encode("utf-8")
            if u8 == u"\u00d7".encode("utf-8"): paraja += 1
            elif u8 >= u"\u0370".encode("utf-8") and u8 <= u"\u03ff".encode("utf-8"): paraja += 1
            elif u8 >= u"\u2000".encode("utf-8") and u8 <= u"\u206f".encode("utf-8"): paraja += 1
            elif u8 >= u"\u2190".encode("utf-8") and u8 <= u"\u22ff".encode("utf-8"): paraja += 1
            elif u8 >= u"\u25a0".encode("utf-8") and u8 <= u"\u25ff".encode("utf-8"): paraja += 1
            elif u8 >= u"\u3000".encode("utf-8") and u8 <= u"\u30ff".encode("utf-8"): paraja += 1
            elif u8 >= u"\u4e00".encode("utf-8") and u8 <= u"\u9fff".encode("utf-8"): paraja += 1
            elif u8 >= u"\uff00".encode("utf-8") and u8 <= u"\uffef".encode("utf-8"): paraja += 1
            else: paranonja += 1
        if paraja:
        #if True or paranonja == 0 or (float(paraja) / float(paranonja)) > 3.0:
            #print self.currenttext
            strpos = 0
            unknown = u""
            english = u""
            japanese = u""
            while strpos < len(self.currenttext): # there's something to match
                strlen, kr, row = self.getamatch4(self.currenttext[strpos:])
                if not strlen: # didn't find any match
                    unknown += self.currenttext[strpos:strpos+1]
                    strpos += 1
                else: # found something!
                    #print self.thisid, self.block, order, row[0][0], row[0][1], unknown, self.currenttext[strpos:strpos+strlen]
                    # FIXME stick all the senses together as one string?
                    # or apply some rules to select one
                    self.ja += strlen
                    self.nonja += len(unknown)
#                    if kanji: kr = "kanji"
#                    else: kr="reading"
                    if order > 0:
                        if unknown != u"" and unknown != u"　":
                            lastquery += ", postunknown='%s'"
                            lastvals += (unknown,)
                        #print lastquery % lastvals
                        self.cursor.execute(lastquery, lastvals)
                    if order == 0 and unknown != u"" and unknown != u"　":
                        lastquery="insert into `" + self.indextable + "` set parsestamp=now(), urlID=%d, block=%d, `order`=%d, jmdictID=%s, jmsenseID=%s, tense='%s', preunknown='%s', kr='%s'"
                        lastvals=(self.thisid, self.block, order, row[0][0], row[0][1], row[0][2], unknown, kr)
                    else:
                        lastquery="insert into `" + self.indextable + "` set parsestamp=now(), urlID=%d, block=%d, `order`=%d, jmdictID=%s, jmsenseID=%s, tense='%s', kr='%s'"
                        lastvals=(self.thisid, self.block, order, row[0][0], row[0][1], row[0][2], kr)
                    order += 1
                    unknown = u""
                    strpos += strlen
            if order:
                if unknown != u"" and unknown != u"　":
                    lastquery += ", postunknown='%s'"
                    lastvals += (unknown,)
                #print lastquery % lastvals
                self.cursor.execute(lastquery, lastvals)
        else: self.nonja += len(self.currenttext)
        self.currenttext = u""
        self.block += 1

    def handle_endtag(self, tag):
        if tag.lower() in self.blocktag and tag.lower() not in self.jointag:
            # process current text string
            if self.currenttext != "": self.process_text()

    def _fixencoding(self, encoding):
        # complete list is here: http://www.iana.org/assignments/character-sets
        # python list is here: http://docs.python.org/lib/standard-encodings.html
        # fix common (and uncommon) mistakes, typos and things missing from python
        # looks like 'ibm_cp943c' is a superset of sjis and cp932 - http://www.bugbearr.jp/?文字化け
        encoding = encoding.lower().replace("-", "_")
        if encoding in ("", "none", "x_sjis", "sjis_jp", "shift_sjis", "x_sjis_jp", "sihft_jis", "windows_31j", "sift_jis", "cp943c") : encoding = "shift_jis"
        elif encoding in ("euc", "x_euc", "x_euc_jp") : encoding = "euc_jp"
        elif encoding in ("iso_8859_8_i") : encoding = "iso8859_8"
        elif encoding in ("windows_874") : encoding = "cp874"
        elif encoding in ("big5_8859_1") : encoding = "big5"
        return encoding

    def handle_starttag(self, tag, attrs):
        if tag.lower() not in self.blocktag and tag.lower() not in self.ignoretag and tag.lower() not in self.inlinetag and tag.lower() not in self.unknowntag and tag.lower() not in self.missedtag:
            self.missedtag.append(tag.lower())
        if tag.lower() in self.blocktag and tag.lower() not in self.jointag:
            # process current text string
            if self.currenttext != "": self.process_text()
        isrobots = False
        contents = ""
        for attr in attrs:
            if attr[0] in self.linktag and attr[1] and not attr[1].startswith("javascript:") and tag.lower() in self.linktag[attr[0]]:
                self.tags.append(attr[1].replace("\n", "").strip())
            elif tag.lower() == 'meta' and len(attr) >= 2 and attr[0] == "content" and attr[1] is not None and attr[1].find("charset=") != -1 :
                self.encoding = self._fixencoding(attr[1].split("charset=")[1])
            elif tag.lower() == 'meta' and len(attr) == 2 and attr[0] == "name" and attr[1] is not None and attr[1]== "robots" : isrobots = True
            elif tag.lower() == 'meta' and len(attr) == 2 and attr[0] == "content" and attr[1] is not None: contents = attr[1]
            elif tag.lower() == 'html' and len(attr) == 2 and attr[0] == "lang" and attr[1] is not None and attr[1].lower() != "ja":
                self.error("not japanese - language '%s'" % attr[1])
        if isrobots and contents.find("noindex") != -1: self.error("meta 'noindex' found")

    def handle_data(self, data):
        if (data in ("/*", "*/")): return
        if (data.isspace()): return
        self.currenttext += data

    def unknown_decl(self, data): # no, i really don't care about these!
        pass

def unquoteutf8(url, encoding = None):
    # RFC3986 says "use UTF-8" .. so we actually ignore encoding
    # 'url' should always be unicode on input but utf-8 should be output for DB
    # however, links in pages _may_ be using the page encoding
    try:
        return urllib.parse.unquote(url.encode(encoding)).decode(encoding).encode("utf-8")
    except: # no encoding or wrong encoding specified - utf-8 .. even if that's what failed!
        return urllib.parse.unquote(url.encode("utf-8"))

# see if there's already an entry which should stop us from checking (again)
# implicitly initialise the entry if it's not already there.
def crawlcheck(db_cursor, url, referrer = None, recent = 0, encoding = None):
    url = unquoteutf8(url, encoding = encoding)
    if globals()['options'].verbose: print ("checking for previous scan of", url)
    if referrer:
        referrer = unquoteutf8(referrer, encoding = encoding)
        db_cursor.execute("select ID from webcrawl where url='%s'", (referrer, ))
        row = db_cursor.fetchone()
        if row : refid = row[0][0]
        # when called with referrer set we never look at the returned value anyway
        else : return None

    # attempt to insert that url -
    insert = "insert into webcrawl set url='%s', stamp=now()"
    params = [url]
    if referrer:
        insert += ", referrer=%s"
        params.append(refid)
    insert += " returning id"
    try:
        db_cursor.execute(insert, params)
        thisis = db_cursor.fetchone()[0]
    except _mysql_exceptions.IntegrityError:
        # hopefully that just means it's already there
        thisis=-1
    if recent:
        db_cursor.execute("select ID from webcrawl where url='%s' and timestampdiff(hour, now(), stamp)<164 and (ja is not null or redirect is not null)", url)
        row = db_cursor.fetchone()
    if recent and row: return None
    if thisis == -1:
        db_cursor.execute("select ID from webcrawl where url='%s'", url)
        row = db_cursor.fetchone()
        if row: return int(row[0][0])
        else:
            print("couln't find or add url", url, referrer, recent)
            return None
    return thisis


def crawlupdate(db_cursor, url, ja=None, redirect = None, status = None, line=None, char=None, details=None, encoding = None):
    url = unquoteutf8(url, encoding = encoding)
    if redirect:
        reid = crawlcheck(redirect)
        redirect = unquoteutf8(redirect, encoding = encoding)
        if reid is None: return None
    if type(status) == unicode: status = status.encode("utf-8") # for DB
    if type(details) == unicode: details = details.encode("utf-8") # for DB

    update = "update webcrawl set stamp=now()"
    params = []
    if redirect:
        update += ", redirect="
        params.append(str(reid))
    if ja is not None:
        update += ", ja=%d"
        params.append(ja)
    if status is not None:
        update += ", status='%s'"
        params.append(status)
    if line is not None:
        update += ", errline=%s"
        params.append(line)
    if char is not None:
        update += ", errchar=%s"
        params.append(char)
    if details is not None:
        update += ", errdetail='%s'"
        params.append(details)
    update += " where url='%s'"
    params.append(url)
    db_cursor.execute(update, params)
    if db_cursor.rowcount != 1: sys.stderr.write("warning: couldn't update crawl status of url '%s' (%s)\n" % (url, update))
    return None

def scan2(dicttable, indextable, url, thisid):
# db connection for the thread
    scan_cursor=py_db.connect(dbname="jmdict").cursor()
    scan_cursorscan_cursor.execute("SET NAMES utf8")
    scan_cursor.execute("SET CHARACTER SET utf8")
    scan_cursor.execute("SET character_set_connection=utf8")
    opener = urllib.request.build_opener()
    opener.addheaders = [('User-agent', 'Mozilla/5.0')] # wikipedia doesn't work without this - gives 403 forbidden

    reader = jaHTMLParser(scan_cursor)
    # grrr.  "instance attributes"??!
    for atype, treads in globals()['vct'].readings.iteritems():
        if atype not in reader.endings:
            if globals()['options'].verbose: print("adding readings for", atype)
            reader.endings[atype] = {}
        elif globals()['options'].verbose: print("updating", atype)
        for btype, reading in treads.iteritems():
            if btype not in reader.endings[atype]:
                if globals()['options'].verbose: print("added ending", btype)
                reader.endings[atype][btype] = reading
            elif globals()['options'].verbose: print("checked", btype)
            if reading != reader.endings[atype][btype]:
                print("please change reading for", atype, btype, "from", reading, "to", reader.endings[atype][btype])
                # looks like the wikipedia table had errors
#                reader.endings[atype][btype] = reading

    reader.tags = []
    reader.ja = 0
    reader.nonja = 0
    reader.block = 0
    reader.dicttable = dicttable
    reader.indextable = indextable
    reader.encoding = "Shift_JIS" # the most common encoding for jp pages which don't specify any encoding
    reader.CDATA_CONTENT_ELEMENTS = [] # don't treat CDATA in <style> amd <script> tags as 'stuff' - they're decls which i'd like to skip.
    reader.missedtag = []
    reader.biggest = globals()['biggest']
    realurl = url
    status = "OK"
    lineno = None
    offset = None
    details = None
    parsetime = timedelta(seconds = 0)

    try:
        urlparts = urlparse(url)
        page = opener.open(urlunparse((urlparts[0], urlparts[1].encode("idna")) +  urlparts[2:]).encode("utf-8"))

        charset = ["utf-8", "Shift_JIS", "euc_jp", "iso8859_8", "cp874", "big5"]
        if "charset=" in page.headers['content-type']:
            charset = [reader._fixencoding(page.headers['content-type'].split('charset=')[-1])] + charset
        # ASSUME geturl returns utf-8??
        # wikipedia returns urlencoded page-encoding (i assume) uri
        realurl = page.geturl().decode("utf-8")
        if realurl != url:
            print("REDIRECT?", url, "=>", realurl)
            crawlupdate(db, url, redirect=realurl, encoding = charset[0])
            thisid = crawlcheck(db, realurl, recent=1)
            if not globals()['options'].force and thisid is None: return parsetime
        if page.info().getheader("Content-Type") and page.info().getheader("Content-Type").split(";")[0] != "text/html":
            crawlupdate(scan_cursor, url, ja=0, status="Content type: " + page.info().getheader("Content-Type").split(";")[0], encoding = charset[0])
            home = "/mnt/stuff/media/web/" + page.info().getheader("Content-Type").split(";")[0]
            cantcreate = False
            try:
                os.makedirs(home)
            except OSError as err:
                if not str(err).startswith("[Errno 17]"): # dir exists
                    sys.stderr.write(str(err) + "\n")
                    cantcreate = True
            if not cantcreate:
                #print home
                pieces = urlparse(url)
                try:
                    os.stat(home + "/"+pieces[1]+pieces[2])
                except: # hopefully "file doesn't already exist"
                           subprocess.check_call(['sh', '/usr/local/bin/get_file', home, url])
            return parsetime
        reader.thisid = thisid
        #print datetime.now(), "scanning", urllib.unquote(realurl)
        parsestart=datetime.now()
        # read sometimes produces weird ValueError: invalid literal for int() with base 16: '' @ httplib.py:548
        # 8oct2010 now feed sometimes produces unicode error in re._compile
        content = page.read()
        # let's guess it's utf-8 and convert to unicode just in case
        # 8oct2011 actually, let's assume urllib2 is doing the right thing and decoding for us
        # or try decoding using trick from stackoverflow 1020892
        # third time lucky - assume web server lied to us - let the reader sort it out
        # problem is html parser can't scan encoded content - tends to fall over on attributes
        decode_errors = {}
        leastworstenc = ""
        leastworst = 0
        while len(charset):
            try:
                content = unicode(content, charset[0])
                reader.encoding = charset[0]
                break
            except LookupError:
                print("unknown encoding in", page.headers['content-type'])
            except UnicodeDecodeError as decstatus:
                decode_errors[charset[0]] = decstatus
                if " in position " in str(decstatus):
                    posn = str(decstatus).split(" in position ")[1].split("-")[0].split(":")[0]
                    if posn.isdigit() and int(posn) > leastworst:
                        leastworst = int(posn)
                        leastworstenc = charset[0]
                    #else: print "decode status no good", decstatus, "best is", leastworst
                else: print("weird decode status", decstatus)
                if len(charset) == 1:
                    if leastworst:
                        print("decoding from", leastworstenc, "with replacements")
                        content = unicode(content, leastworstenc, "replace")
                        reader.encoding = leastworstenc
                    else:
                        print("failed character decoding:")
                        for k in decode_errors:
                            print(k, decode_errors[k])
                        raise
            charset = charset[1:]
        reader.feed(content)
        reader.close()
        parsetime=datetime.now() - parsestart

    except ValueError as status:
        print(traceback.format_exc())
        status = str(status)
    except socket.timeout:
        status = "Connection: no response from server - timed out"
    except socket.error as e:
        status = str(e)
    except socket.gaierror as e:
        status = str(e)
    except urllib.error.HTTPError as e:
        if hasattr(e, "reason"): status = "HTTP: " + e.reason
        else: status = "HTTP %d" % e.code
    except urllib.error.URLError as e:
        # URLError.reason appears to be another object - timeout, gaierror etc
            # those are the socket exceptions: error, herror, gaierror and timeout
        #if hasattr(e, "reason"): status = "URL error: " + e.reason
        # ah - but it doesn't have a 'code' either!
        #status = "URL %d" % e.code
        status = "URL: " + str(type(e.reason))

    globals()['biggest'] = reader.biggest
    for a in reader.missedtag:
        print("unhandled element:", a)
    if reader.nonja + reader.ja == 0: japness = 0
    else : japness = float(100 * reader.ja) / float(reader.nonja + reader.ja)
    # log url to DB with timestamp and ja score
    if globals()['options'].showpages: print(unquoteutf8(realurl, encoding = reader.encoding), status, "ja = %.1f" % japness)
    thisID = crawlupdate(db, realurl, ja=japness, status=status, line=lineno, char=offset, details=details, encoding = reader.encoding)
    #if status != "OK": print urllib.unquote(realurl), "is how japanese (CJK)? .. %d%%" % japness, status
    # if it's japanese enough and we've not gone too deep and we've not seen it before (recently) then follow the link
    if japness > 25:
        #print reader.encoding
        for child in reader.tags:
            # if child is http://something where something contains no / then add a trailing /
            if child[0:7] == "http://" and child[7:].find("/") == -1: child += "/"
            if child[0:8] == "https://" and child[8:].find("/") == -1: child += "/"
            child = urljoin(realurl, child).replace("/..", "")
            if child[0:7] == "http://" and child[7:].find("/") == -1: child += "/"
            if child[0:8] == "https://" and child[8:].find("/") == -1: child += "/"
            try:
                parts = urlparse(child)
                newchild = parts[0] + "://" + parts[1]
                if parts[2][0] != "/": newchild += "/"
                newchild += parts[2]
                if parts[3]: newchild += ";" + parts[3]
                if parts[4]: newchild += "?" + parts[4]
                if parts[0] in ("http", "https"):
                    crawlcheck(db, url = newchild, referrer = realurl, encoding = reader.encoding)
                    if globals()['options'].links: print(urllib.parse.unquote(newchild))
            except IndexError: # error in urlparse that tries to 'find' on a None value
                print(urllib.parse.unquote(realurl), " - problem parsing child: ", child)
                crawlcheck(db, url = child, referrer = realurl, encoding = reader.encoding)
            # if the child isn't japanese enough then modify rules accordingly
    # otherwise make a note of the urls you've not followed with a timestamp and ref to the page that wasn't japanese enough
        # then if you get to one of those pages by another route and find it's good you can modify the rules accordingly
            # we like self-tuning algorithms :-)
    return parsetime

def threadscan(dicttable, indextable, url, thisid):
    threads = globals()['threads']
    running = 0
    while not running:
        for threadnum in range(0,16):
            if not threads[threadnum] or not threads[threadnum].isAlive():
                threads[threadnum] = threading.Thread(group=None, target=scan2, kwargs={'dicttable':dicttable, 'indextable':indextable, 'url':url, 'thisid':thisid})
                threads[threadnum].start()
                running = 1
                break
        if not running:
            time.sleep(1)

def scan(dicttable, indextable, url = None, pref = None):
    lasttime = scanstart = datetime.now()
    # if url is blank
        # try random http://www.*, non-wikipedia entries first
        # pick a random url with no 'ja' score set and a referrer with a ja score above min-referrer
        # if there aren't any then pick the oldest url more than 1 week old
        # if there aren't any of them then just return
    # otherwise use the supplied url but check
    # possibly we should avoid things from all domains in referrer is null
    # weight against popular domains - to avoid hammering most popular one
    # use weight rather than if...else otherwise you have to grep the entire web before you get any wikipedia pages!
    if url:
        url.strip()
        thisid = crawlcheck(db, url, recent= not globals()['options'].force)
        if thisid is None: return None
        picktime = datetime.now() - scanstart
        parsetime = scan2(dicttable, indextable, url, thisid)
    else:
        parsetime = timedelta(seconds = 0)
        if pref:
            if globals()['options'].verbose: print("finding up to 1000 'preferred' pages to scan")
            cursor.execute("select a.url, b.url, a.ID from webcrawl a left join webcrawl b on b.ID=a.referrer where a.ja is null and a.redirect is null and a.url like '%" + pref + "%' order by rand() limit 1000")
            row = cursor.fetchone()
        else: row = None
        if not row:
            if globals()['options'].verbose: print("finding up to 1000 other pages to scan")
            cursor.execute("""select a.url, b.url,a.ID from webcrawl a left join webcrawl b on b.ID=a.referrer where a.ja is null and a.redirect is null order by floor(b.ja / 10) + rand() desc limit 1000""")
            row = cursor.fetchone()
        if not row : return None
        picktime = datetime.now() - scanstart
        lastrowcount = rowcount = 0
        jacount = 0
        while row:
            url = row[0][0].decode("utf-8")
            if globals()['options'].test:
                print("scanning", url, "which we got from", row[0][1])
                parsetime = timedelta(seconds = 0)
            else:
                thisid = int(row[0][2])
                parsetime = scan2(dicttable, indextable, url, thisid)
                #threadscan(dicttable, indextable, url, thisid)
            rowcount += 1
            #if parsetime != timedelta(seconds = 0): jacount += 1
            if (datetime.now() - lasttime).seconds > 360:
                lasttime = datetime.now()
                print(lasttime, rowcount, rowcount-lastrowcount, (datetime.now() - scanstart) / rowcount)
                jacount = 0
                lastrowcount=rowcount
            row = res.fetchone()

        return [datetime.now() - scanstart, picktime, parsetime]


parser = OptionParser()
parser.add_option("-d", "--dataset", dest="dictid", type='long', help="dataset ID for the jmdict table")
parser.add_option("-i", "--index", dest="index", help="index table for the jmdict table - ignored if there's only one index linked to your jmdict table")
parser.add_option("-u", "--url", dest="url", help="specific URL to scan first")
parser.add_option("-r", "--recursive", action="store_true", dest="recursive", default=False, help="crawl the web")
parser.add_option("-n", "--new", dest="new", help="tablename for a new index")
parser.add_option("-p", "--pref", dest="preferred", help="part of URL to prefer when selecting a link to follow")
parser.add_option("-f", "--force", action="store_true", dest="force", default=False, help="scan page even if it's already been scanned")
parser.add_option("-t", "--test", action="store_true", dest="test", default=False, help="just say what you would do and why")
parser.add_option("-s", "--showpages", action="store_true", dest="showpages", default=False, help="display pages scanned")
parser.add_option("-l", "--links", action="store_true", dest="links", default=False, help="list all links")
parser.add_option("-v", "--verbose", action="store_true", dest="verbose", default=False, help="give detailed output")
(options, args) = parser.parse_args()

if not options.dictid:
    print("you must specify a jmdict table.  use -h for details.")
    sys.exit(1)

print("getting conjugation table from web...")
opener = urllib.request.build_opener()
opener.addheaders = [('User-agent', 'Mozilla/5.0')] # wikipedia doesn't work without this - gives 403 forbidden

# grrr.  "instance attributes"??!
# update readings table from http://en.wikibooks.org/wiki/Japanese/Verb_conjugation_table
vct = vctHTMLParser()
#vct.feed(opener.open("http://en.wikibooks.org/wiki/Japanese/Verb_conjugation_table").read())
# FIXME: the table format has been updated - cheat for now and use the old version
vct.feed(
    opener.open(
        "http://en.wikibooks.org/w/index.php?title=Japanese/Verb_conjugation_table&oldid=1272624"
    ).read().decode("utf-8")
)
threads = [None, None, None, None, None, None, None, None, None, None, None, None, None, None, None, None, None, None, None, None, None, None, None, None, None, None, None, None, None, None, None, None]
cursor=py_db.connect(dbname="jmdict").cursor()
cursor.execute("SET NAMES 'UTF8'")
# get tablenames for dict and index from dict ID
cursor.execute("select tablename from WEBUSERS.DATASETS where ID=%s" % options.dictid)
row = cursor.fetchone()
if not row:
    print("dict not found - sure you got the ID right?")
    sys.exit(1)
fromdict = row[0][0]
print("finding longest word...")
cursor.execute("select max(char_length(kanji)) from USERDATA.`%s`" % fromdict)
biggest = int(cursor.fetchone()[0][0])
print("finding longest reading...")
cursor.execute("select max(char_length(reading)) from USERDATA.`%s`" % fromdict)
bigr = int(cursor.fetchone()[0][0])
if bigr > biggest: biggest = bigr
fromindexlist = []
cursor.query("select distinct tablename from WEBUSERS.JOINS, WEBUSERS.DATASETS where datasetIDa=%s and datasetIDb=ID" % options.dictid)
row = cursor.fetchone()
while row:
    fromindexlist.append(row[0][0])
    row = cursor.fetchone()
cursor.query("select distinct tablename from WEBUSERS.JOINS, WEBUSERS.DATASETS where datasetIDb=%s and datasetIDa=ID" % options.dictid)
row = cursor.fetchone()
while row:
    fromindexlist.append(row[0][0])
    row = cursor.fetchone()
if len(fromindexlist) == 0 or options.new:
    if options.new: fromindex = options.new
    else: fromindex = fromdict + "jpindex"
    try:
        cursor.execute("""CREATE TABLE `USERDATA`.`%s` (
      `urlID` bigint(20) unsigned NOT NULL,
      `block` int(11) NOT NULL,
      `order` int(10) unsigned NOT NULL,
      `jmdictID` int(10) unsigned NOT NULL,
      `jmsenseID` int(10) unsigned NOT NULL,
      `tense` varchar(16) NOT NULL,
      `kr` enum('kanji','reading') NOT NULL,
      `preunknown` varchar(128) character set utf8 default NULL,
      `postunknown` varchar(128) character set utf8 default NULL,
      `parsestamp` datetime NOT NULL,
      KEY `url` USING BTREE (`urlID`,`block`,`order`),
      KEY `jmdict` USING BTREE (`jmdictID`,`jmsenseID`,`tense`,`kr`)
    ) ENGINE=MyISAM DEFAULT CHARSET=latin1 COMMENT='index of jmdict words in webcrawl pages'""" % fromindex)
    except:
        print("failed to create index table `%s`" % fromindex)
        sys.exit(1)
    cursor.execute("insert into WEBUSERS.DATASETS set tablename='%s', stamp=now(), userid=0, status='loading' returning id" % fromindex)
    toindexid = cursor.fetchone()[0]
    print("created dataset %d for new index" % toindexid)
    # make a set of 3 JOINS records for it
    cursor.execute("insert into WEBUSERS.JOINS set datasetIDa=%s, datasetIDb=%d, columna='jmdictID', columnb='jmdictID'" % (options.dictid, toindexid))
    cursor.execute("insert into WEBUSERS.JOINS set datasetIDa=%s, datasetIDb=%d, columna='senseID', columnb='jmsenseID'" % (options.dictid, toindexid))
    cursor.execute("insert into WEBUSERS.JOINS set datasetIDa=%s, datasetIDb=%d, columna='tense', columnb='tense'" % (options.dictid, toindexid))
elif len(fromindexlist) == 1: fromindex = fromindexlist[0]
else:
    if options.index:
        if options.index not in fromindexlist:
            print(str(options.index) + " isn't a valid index for your jmdict table. valid index tables:", ", ".join(fromindexlist))
            sys.exit(1)
        else: fromindex = options.index
    else:
        print("found too many possible index tables - use -i/--index to choose one or -n/--new to create a new one:", ", ".join(fromindexlist))
        sys.exit(1)

print("using %s and %s" % (fromdict, fromindex))

socket.setdefaulttimeout(5) # if pages don't respond within 5s then skip them

#start here!
# seed the database with the links from a few key pages
if options.url: scan(url = options.url, dicttable = fromdict, indextable = fromindex, pref = options.preferred)
elif options.new: scan(url = "http://ja.wikipedia.org", dicttable = fromdict, indextable = fromindex, pref = options.preferred)
# then crawl
if options.recursive:
    while scan(dicttable = fromdict, indextable = fromindex, pref = options.preferred): pass
cursor.close()

