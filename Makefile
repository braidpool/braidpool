# @file Makefile
#
# Makefile for typesetting LaTeX documents. Requires GNU Make 3.81 on Linux.
# See "make help".
#
# This file is provided under the MIT License:
#
# MIT License
#
# Copyright (c) 2018-2020 Takahiro Ueda
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.
#

MAKEFILE4LATEX_VERSION = 0.5.0

define help_message
Makefile for LaTeX ($(MAKEFILE4LATEX_VERSION))

Usage
  make [<targets...>]

Targets
  all (default):
    Build all documents in the current directory.

  all-recursive:
    Build all documents in the source tree.

  dvi, ps, pdf, eps, svg, jpg, png:
    Build all documents with the specified file format in the current directory.

  help:
    Show this message.

  clean:
    Delete all files created by this Makefile.

  mostlyclean:
    Delete only intermediate files created by this Makefile.

  lint:
    Run linters for source files in the current directory.

  dist:
    Create tar-gzipped archives for arXiv submission.

  watch:
    Watch the changes and automatically rebuild documents.

  upgrade:
    Upgrade the setup.

See also
  https://github.com/tueda/makefile4latex
endef

# The default target of this Makefile tries to create this type of files from
# all *.tex:
# - dvi
# - ps
# - pdf (default)
default_target = pdf

# The toolchain for typesetting:
# - latex_dvips
# - latex_dvipdf
# - platex_dvips
# - platex_dvipdfmx
# - uplatex_dvips
# - uplatex_dvipdfmx
# - pdflatex (default)
# - xelatex
# - lualatex
# - luajitlatex
# Aliases:
# - latex -> latex_dvips
# - platex -> platex_dvips
# - uplatex -> uplatex_dvips
TOOLCHAIN = pdflatex

# Specify a commit range for latexdiff.
DIFF =

# Number of iterations for typesetting.
MAXREPEAT = 5

# Build directory.
BUILDDIR =

# Use latex-dev if DEV is defined.
DEV =

# (for debugging) Keep temporary directories if its value is non-empty.
KEEP_TEMP =

# Specify the color mode in the output:
# - always
# - never
# - auto (default)
COLOR =

# Files not to be included in a distribution.
NODISTFILES =

# Extra files to be included in a distribution.
EXTRADISTFILES =

# Files to be copied in "anc" directory in a distribution.
ANCILLARYFILES =

# Additional files to mostly-clean.
MOSTLYCLEANFILES =

# Additional files to clean.
CLEANFILES =

# Additional directories to mostly-clean.
MOSTLYCLEANDIRS =

# Additional directories to clean.
CLEANDIRS = .cache _cache cache

# Prerequisite Make targets in the current directory.
PREREQUISITE =

# Prerequisite Make targets in subdirectories.
PREREQUISITE_SUBDIRS = NONE

# List of linter commands/rules, invoked by "make lint".
LINTS = chktex

# List of test scripts/rules, invoked by "make check".
TESTS =

# Options for test scripts. Called as $(call TESTS_OPT,test_name,test_param).
TESTS_OPT =

# List of command line parameters for test scripts. If not empty, test scripts
# will be executed for each parameter.
TESTS_PARAMS =

# The following variables will be guessed if empty.
# XXX: in the current implementation, $(init_toolchain) overrides some of them.
TARGET =
SUBDIRS =
LATEX =
DVIPS =
DVIPDF =
PS2PDF =
DVISVGM =
PDFTOPPM =
GS =
BIBTEX =
BIBER =
SORTREF =
MAKEINDEX =
MAKEGLOSSARIES =
BIB2GLS =
CHKTEX =
ASPELL =
TEXTLINT =
REDPEN =
KPSEWHICH =
AXOHELP =
PDFCROP =
EBB =
EXTRACTBB =
CONVBKMK =
LATEXPAND =
LATEXDIFF =
SOFFICE =
WGET =
CURL =

# Command options.
LATEX_OPT = -interaction=nonstopmode -halt-on-error
PDFLATEX_DVI_OPT = -output-format=dvi
DVIPS_OPT = -Ppdf -z
DVIPDF_OPT =
PS2PDF_OPT = -dPDFSETTINGS=/prepress -dEmbedAllFonts=true
DVISVGM_OPT = -n
PDFTOPPM_OPT = -singlefile
PDFTOPPM_JPG_OPT = -jpeg
PDFTOPPM_PNG_OPT = -png
GS_OPT =
BIBTEX_OPT =
BIBER_OPT =
SORTREF_OPT =
MAKEINDEX_OPT =
MAKEGLOSSARIES_OPT =
BIB2GLS_OPT =
CHKTEX_OPT =
ASPELL_OPT =
TEXTLINT_OPT = --cache
REDPEN_OPT =
KPSEWHICH_OPT =
AXOHELP_OPT =
PDFCROP_OPT =
EBB_OPT =
EXTRACTBB_OPT =
CONVBKMK_OPT = -g
LATEXPAND_OPT = --expand-usepackage
LATEXDIFF_OPT =
SOFFICE_OPT =
WGET_OPT =
CURL_OPT =

# ANSI escape code for colorization.
CL_NORMAL = [0m
CL_NOTICE = [32m
CL_WARN   = [35m
CL_ERROR  = [31m

.SUFFIXES:
.SUFFIXES: .log .bb .xbb .pdf .odt .eps .ps .jpg .png .svg .dvi .fmt .tex .cls .sty .ltx .dtx

DEPDIR = .dep
DIFFDIR = .diff

# $(call cache,VARIABLE) expands $(VARIABLE) with caching.
# See https://www.cmcrossroads.com/article/makefile-optimization-eval-and-macro-caching
cache = $(if $(is_cached-$1),,$(eval is_cached-$1 := 1)$(eval cached_val-$1 := $($1)))$(cached_val-$1)

# $(call type,EXEC-FILE) gives the path to the executable if found,
# otherwise empty.
type = $(if $(strip $1),$(strip \
	$(eval type_retval := $(shell which '$(strip $1)' 2>/dev/null)) \
	$(if $(filter-out $(firstword $(type_retval)),$(type_retval)), \
		$(eval type_retval := '$(type_retval)') \
	) \
	$(type_retval) \
))

# $(call switch,STRING,STRING1,VALUE1,STRING2,VALUE2,...) evaluates the value of
# VALUEi corresponding to the first STRINGi that matches to STRING.
# Limitation: up to 4 STRING-VALUE pairs.
switch = \
	$(if $(filter $2,$1),$3, \
		$(if $(filter $4,$1),$5, \
			$(if $(filter $6,$1),$7, \
				$(if $(filter $8,$1),$9, \
				) \
			) \
		) \
	)

# $(call pathsearch,PROG-NAME,NOERROR-IF-NOT-FOUND,NAME1,...) tries to find
# the given executable.
# Limitation: up to 7 NAMEs.
pathsearch = $(strip \
	$(eval retval := ) \
	$(call pathsearch_impl,$3,$4,$5,$6,$7,$8,$9) \
	$(if $2$(retval),,$(eval retval := \
		$(call error_message,$1 not found); \
		exit 1; :)) \
	$(retval) \
)

pathsearch_impl = \
	$(if $(retval),,$(eval retval := $(call type,$1))) \
	$(if $(retval),,$(if $(strip $2 $3 $4 $5 $6 $7 $8 $9),$(call pathsearch_impl,$2,$3,$4,$5,$6,$7,$8,$9)))

# $(target) gives all targets.
target = $(call cache,target_impl)

target_impl = $(strip \
	$(target_impl_from_ltx) \
	$(target_impl_from_tex) \
)

target_impl_from_ltx = $(srcltxfiles:.ltx=.fmt)

target_impl_from_tex = $(strip \
	$(eval retval := ) \
	$(if $(retval),,$(eval retval := $(TARGET))) \
	$(if $(retval),,$(eval retval := $(srctexfiles:.tex=.$(default_target)))) \
	$(retval) \
)

# $(target_basename) gives the result of $(basename $(target)).
target_basename = $(call cache,target_basename_impl)

target_basename_impl = $(basename $(target))

# $(srctexfiles) gives all LaTeX source files.
# They have the ".tex" file extension and
# (1) contain "documentclass", or
# (2) begin with "%&" (including a format file).
srctexfiles = $(call cache,srctexfiles_impl)

srctexfiles_impl = $(strip $(sort \
	$(shell grep documentclass -l *.tex 2>/dev/null) \
	$(shell awk 'FNR==1{if ($$0~"%&") print FILENAME;}' *.tex 2>/dev/null) \
))

# $(srcltxfiles) gives all .ltx files.
srcltxfiles = $(call cache,srcltxfiles_impl)

srcltxfiles_impl = $(wildcard *.ltx)

# $(srcdtxfiles) gives all .dtx files.
srcdtxfiles = $(call cache,srcdtxfiles_impl)

srcdtxfiles_impl = $(wildcard *.dtx)

ifneq ($(DIFF),)

# $(diff_target) gives all latexdiff target files.
diff_target = $(call cache,diff_target_impl)

diff_target_impl = $(strip $(shell \
	$(call get_rev,$(DIFF),_rev1,_rev2,false); \
	if [ -n "$$_rev1" ]; then \
		for _f in $(srctexfiles); do \
			if [ -z "$$_rev2" ]; then \
				if git show "$$_rev1:./$$_f" >/dev/null 2>&1; then \
					echo $${_f%.*}-diff.$(default_target); \
				fi; \
			else \
				if git show "$$_rev1:./$$_f" >/dev/null 2>&1 && git show "$$_rev2:./$$_f" >/dev/null 2>&1; then \
					echo $${_f%.*}-diff.$(default_target); \
				fi ; \
			fi; \
		done; \
	fi \
))

# $(call get_rev,REV-STR,REV1-VAR,REV2-VAR) decomposes the given Git revision(s)
# into 2 variables.
# $(call get_rev,REV-STR,REV1-VAR,REV2-VAR,false) performs the same but without
# checking the revision string.
get_rev = \
	$(if $4,, \
		if [ -z "$1" ]; then \
			$(call error_message,Git revision not given); \
			exit 1; \
		fi; \
	) \
	$2=; \
	$3=; \
	if expr "$1" : '.*[^.]\.\.[^.]' >/dev/null; then \
		$2=$$(expr "$1" : '\(.*[^.]\)\.\.'); \
		$3=$$(expr "$1" : '.*[^.]\.\.\([^.].*\)'); \
	elif expr "$1" : '.*[^.]\.\.$$' >/dev/null; then \
		$2=$$(expr "$1" : '\(.*[^.]\)\.\.'); \
	else \
		$2="$1"; \
	fi; \
	if [ -n "$$$2" ]; then \
		if git cat-file -e "$$$2" 2>/dev/null; then :; else \
			$(call error_message,invalid Git revision: $$$2); \
			exit 1; \
		fi; \
	fi; \
	if [ -n "$$$3" ]; then \
		if git cat-file -e "$$$3" 2>/dev/null; then :; else \
			$(call error_message,invalid Git revision: $$$3); \
			exit 1; \
		fi; \
	fi

endif

# $(subdirs) gives all subdirectories.
subdirs = $(call cache,subdirs_impl)

subdirs_impl = $(strip \
	$(eval retval := ) \
	$(if $(retval),,$(eval retval := $(SUBDIRS))) \
	$(if $(retval),,$(eval retval := $(dir $(wildcard */Makefile)))) \
	$(retval) \
)

# $(call run_testsuite,PREFIX) runs all rules for targets starting with PREFIX
# in the current Makefile.
# $(run_testsuite) is equivalent to $(call run_testsuite,test_).
run_testsuite = \
	for test in $(call all_testsuite,$(if $1,$1,test_)); do \
		echo "Testing $$test..."; \
		$(MAKE) --silent clean; \
		$(MAKE) --always-make --no-print-directory $$test || exit 1; \
	done

all_testsuite = $(shell $(MAKE) -pq _FORCE | sed -n '/^$1/p' | sed 's/:.*//')

assert_true = \
	$(if $(strip $1),:,false)

assert_false = \
	$(if $(strip $1),false,:)

assert_success = \
	$(strip $1)

assert_fail = \
	if { $(strip $1); }; then false; else :; fi

# $(is_texlive) is "1" if TeX Live is used, otherwise empty.
is_texlive = $(call cache,is_texlive_impl)

is_texlive_impl = $(strip \
	$(shell $(TEX) --version 2>/dev/null | grep -q 'TeX Live' && echo 1) \
)

# $(has_gnu_grep) is "1" if GNU grep is available, otherwise empty.
has_gnu_grep = $(call cache,has_gnu_grep_impl)

has_gnu_grep_impl = $(strip \
	$(shell grep --version 2>/dev/null | grep -q 'GNU' && echo 1) \
)

# $(call rule_exists,RULE) is "1" if RULE exists, otherwise empty.
rule_exists = \
	$(shell $(MAKE) -n $1 >/dev/null 2>&1 && echo 1)

# $(init_toolchain) initializes the toolchain.
init_toolchain = $(call cache,init_toolchain_impl)

init_toolchain_impl = $(strip \
	$(eval $(init_toolchain_$(TOOLCHAIN))) \
	$(if $(typeset_mode),,$(error unknown TOOLCHAIN=$(TOOLCHAIN))) \
)

init_toolchain_latex = \
	$(init_toolchain_latex_dvips)

init_toolchain_latex_dvips = \
	$(eval typeset_mode = dvips) \
	$(eval tex_format = latex)

init_toolchain_latex_dvipdf = \
	$(eval typeset_mode = dvipdf) \
	$(eval tex_format = latex)

init_toolchain_platex = \
	$(init_toolchain_platex_dvips)

init_toolchain_platex_dvips = \
	$(eval typeset_mode = dvips_convbkmk) \
	$(eval tex_format = platex) \
	$(eval LATEX = platex) \
	$(eval BIBTEX = pbibtex) \
	$(eval MAKEINDEX = mendex)

init_toolchain_platex_dvipdfmx = \
	$(eval typeset_mode = dvipdf) \
	$(eval tex_format = platex) \
	$(eval LATEX = platex) \
	$(eval DVIPDF = dvipdfmx) \
	$(eval BIBTEX = pbibtex) \
	$(eval MAKEINDEX = mendex)

init_toolchain_uplatex = \
	$(init_toolchain_uplatex_dvips)

init_toolchain_uplatex_dvips = \
	$(eval typeset_mode = dvips_convbkmk) \
	$(eval tex_format = uplatex) \
	$(eval LATEX = uplatex) \
	$(eval BIBTEX = upbibtex) \
	$(eval MAKEINDEX = upmendex)

init_toolchain_uplatex_dvipdfmx = \
	$(eval typeset_mode = dvipdf) \
	$(eval tex_format = uplatex) \
	$(eval LATEX = uplatex) \
	$(eval DVIPDF = dvipdfmx) \
	$(eval BIBTEX = upbibtex) \
	$(eval MAKEINDEX = upmendex)

init_toolchain_pdflatex = \
	$(eval typeset_mode = pdflatex) \
	$(eval tex_format = pdflatex) \
	$(eval LATEX = pdflatex)

init_toolchain_xelatex = \
	$(eval typeset_mode = pdflatex) \
	$(eval tex_format = xelatex) \
	$(eval LATEX = xelatex)

init_toolchain_lualatex = \
	$(eval typeset_mode = pdflatex) \
	$(eval tex_format = lualatex) \
	$(eval LATEX = lualatex) \
	$(eval BIBTEX = upbibtex) \
	$(eval MAKEINDEX = upmendex)

init_toolchain_luajitlatex = \
	$(eval typeset_mode = pdflatex) \
	$(eval tex_format = luajitlatex) \
	$(eval LATEX = luajittex) \
	$(eval LATEX_OPT := --fmt=luajitlatex.fmt $(LATEX_OPT)) \
	$(eval BIBTEX = upbibtex) \
	$(eval MAKEINDEX = upmendex)

# The typeset mode: "dvips" or "dvips_convbkmk" or "dvipdf" or "pdflatex".
typeset_mode =

# The TeX format.
tex_format =

# $(call pathsearch2,PROG-NAME,VAR-NAME,NAME1,...) is basically pathsearch after
# calling init_toolchain.
pathsearch2 = $(strip \
	$(init_toolchain) \
	$(call pathsearch,$1,,$($2),$3,$4,$5,$6,$7,$8,$9) \
)

# $(latex)
latex = $(call cache,latex_impl)

latex_impl = $(strip \
	$(latex_noopt) $(LATEX_OPT) \
	$(if $(findstring -recorder,$(LATEX_OPT)),,-recorder) \
)

# (latex_noopt) doesn't include $(LATEX_OPT).
latex_noopt = $(call cache,latex_noopt_impl)$(if $(BUILDDIR), -output-directory=$(BUILDDIR))

latex_noopt_impl = $(init_toolchain)$(call pathsearch,latex$(if $(DEV),-dev),,$(LATEX)$(if $(DEV),-dev),latex$(if $(DEV),-dev))

# $(dvips)
dvips = $(call cache,dvips_impl) $(DVIPS_OPT)

dvips_impl = $(call pathsearch2,dvips,DVIPS,dvips,dvipsk)

# $(dvipdf)
dvipdf = $(call cache,dvipdf_impl) $(DVIPDF_OPT)

dvipdf_impl = $(call pathsearch2,dvipdf,DVIPDF,dvipdf,dvipdfm,dvipdfmx)

# $(ps2pdf)
ps2pdf = $(call cache,ps2pdf_impl) $(PS2PDF_OPT)

ps2pdf_impl = $(call pathsearch2,ps2pdf,PS2PDF,ps2pdf)

# $(dvisvgm)
dvisvgm = $(call cache,dvisvgm_impl) $(DVISVGM_OPT)

dvisvgm_impl = $(call pathsearch2,dvisvgm,DVISVGM,dvisvgm)

# $(pdftoppm)
pdftoppm = $(call cache,pdftoppm_impl) $(PDFTOPPM_OPT)

pdftoppm_impl = $(call pathsearch2,pdftoppm,PDFTOPPM,pdftoppm)

# $(gs)
gs = $(call cache,gs_impl) $(GS_OPT)

gs_impl = $(call pathsearch2,gs,GS,gs,gswin32,gswin64,gsos2)

# $(bibtex)
bibtex = $(call cache,bibtex_impl) $(BIBTEX_OPT)

bibtex_impl = $(call pathsearch2,bibtex,BIBTEX,bibtex)

# $(biber)
biber = $(call cache,biber_impl) $(BIBER_OPT)

biber_impl = $(call pathsearch2,biber,BIBER,biber)

# $(sortref)
sortref = $(call cache,sortref_impl) $(SORTREF_OPT)

sortref_impl = $(call pathsearch2,sortref,SORTREF,sortref)

# $(makeindex)
makeindex = $(call cache,makeindex_impl) $(MAKEINDEX_OPT)

makeindex_impl = $(call pathsearch2,makeindex,MAKEINDEX,makeindex)

# $(makeglossaries)
makeglossaries = $(call cache,makeglossaries_impl) $(MAKEGLOSSARIES_OPT)

makeglossaries_impl = $(call pathsearch2,makeglossaries,MAKEGLOSSARIES,makeglossaries)

# $(bib2gls)
bib2gls = $(call cache,bib2gls_impl) $(BIB2GLS_OPT)

bib2gls_impl = $(call pathsearch2,bib2gls,BIB2GLS,bib2gls)

# $(chktex)
chktex = $(call cache,chktex_impl) $(CHKTEX_OPT)

chktex_impl = $(call pathsearch2,chktex,CHKTEX,chktex)

# $(aspell)
aspell = $(call cache,aspell_impl) $(ASPELL_OPT)

aspell_impl = $(call pathsearch2,aspell,ASPELL,aspell)

# $(textlint)
textlint = $(call cache,textlint_impl) $(TEXTLINT_OPT)

textlint_impl = $(call pathsearch2,textlint,TEXTLINT,node_modules/.bin/textlint,\
$(shell git rev-parse --show-toplevel 2>/dev/null)/node_modules/.bin/textlint,\
$(shell git rev-parse --show-superproject-working-tree 2>/dev/null)/node_modules/.bin/textlint,\
../node_modules/.bin/textlint,\
../../node_modules/.bin/textlint,\
textlint)

# $(redpen)
redpen = $(call cache,redpen_impl) $(REDPEN_OPT)

redpen_impl = $(call pathsearch2,redpen,REDPEN,redpen)

# $(kpsewhich)
kpsewhich = $(call cache,kpsewhich_impl) $(KPSEWHICH_OPT)

kpsewhich_impl = $(call pathsearch2,kpsewhich,KPSEWHICH,kpsewhich)

# $(axohelp)
axohelp = $(call cache,axohelp_impl) $(AXOHELP_OPT)

axohelp_impl = $(call pathsearch2,axohelp,AXOHELP,axohelp)

# $(pdfcrop)
pdfcrop = $(call cache,pdfcrop_impl) $(PDFCROP_OPT)

pdfcrop_impl = $(call pathsearch2,pdfcrop,PDFCROP,pdfcrop)

# $(ebb)
ebb = $(call cache,ebb_impl) $(EBB_OPT)

ebb_impl = $(call pathsearch2,ebb,EBB,ebb)

# $(extractbb)
extractbb = $(call cache,extractbb_impl) $(EXTRACTBB_OPT)

extractbb_impl = $(call pathsearch2,extractbb,EXTRACTBB,extractbb)

# $(convbkmk)
convbkmk = $(call cache,convbkmk_impl) $(CONVBKMK_OPT)

convbkmk_impl = $(call pathsearch2,convbkmk,CONVBKMK,convbkmk)

# $(latexpand)
latexpand = $(call cache,latexpand_impl) $(LATEXPAND_OPT)

latexpand_impl = $(call pathsearch2,latexpand,LATEXPAND,latexpand)

# $(latexdiff)
latexdiff = $(call cache,latexdiff_impl) $(LATEXDIFF_OPT)

latexdiff_impl = $(call pathsearch2,latexdiff,LATEXDIFF,latexdiff)

# $(download) <OUTPUT-FILE> <URL>
download = $(strip \
	$(if $(_download_wget_found)$(_download_curl_found),,$(call _download_init)) \
	$(if $(_download_wget_found), \
		$(_download_wget_found) $(WGET_OPT) -O \
	, \
		$(if $(_download_curl_found), \
			$(_download_curl_found) $(CURL_OPT) -L -o \
		, \
			$(call error_message,both wget and curl not found); exit 1; \
		) \
	) \
)

_download_init = $(strip \
	$(if $(_download_wget_found),,$(eval _download_wget_found := $(call pathsearch,wget,true,$(WGET),wget))) \
	$(if $(_download_wget_found)$(_download_curl_found),,$(eval _download_curl_found := $(call pathsearch,curl,true,$(CURL),curl))) \
)

_download_wget_found =
_download_curl_found =

# $(soffice)
soffice = $(call cache,soffice_impl) $(SOFFICE_OPT)

soffice_impl = $(call pathsearch2,soffice,SOFFICE, \
	soffice, \
	/cygdrive/c/Program Files/LibreOffice 6/program/soffice, \
	/cygdrive/c/Program Files (x86)/LibreOffice 6/program/soffice, \
	/cygdrive/c/Program Files/LibreOffice 5/program/soffice, \
	/cygdrive/c/Program Files (x86)/LibreOffice 5/program/soffice, \
	/cygdrive/c/Program Files/LibreOffice 4/program/soffice, \
	/cygdrive/c/Program Files (x86)/LibreOffice 4/program/soffice \
)

# $(Makefile) gives the name of this Makefile.
Makefile = $(call cache,Makefile_impl)

Makefile_impl = $(firstword $(MAKEFILE_LIST))

# $(mostlycleanfiles) gives all intermediately generated files, to be deleted by
# "make mostlyclean".
#   .aux - LaTeX auxiliary file
#   .auxlock - TikZ externalization aux file lock
#   .ax1 - axodraw2 auxiliary (axohelp input) file
#   .ax2 - axohelp output file
#   .bbl - BibTeX output file
#   .bcf - by biblatex package
#   .blg - BibTeX log file
#   .end - ?
#   .fls - LaTeX recorder file
#   .fmt - TeX format file
#   .glg - glossary log file
#   .glo - glossary entries
#   .gls - glossary output
#   .glsdefs - glossary output
#   .glstex - by bib2gls
#   .idx - index entries
#   .ilg - index log file
#   .ind - index output
#   .ist - index style file
#   .lof - list of figures
#   .log - (La)TeX log file
#   .lot - list of tables
#   .nav - Beamer navigation items
#   .out - Beamer outlines
#   .run.xml - by logreq package
#   .snm - Beamer page labels
#   .spl - by elsarticle class
#   .toc - table of contents
#   .*.vrb - Beamer verbatim materials
#   .xdy - by xindy
#   Notes.bib - by revtex package
#   *-blx.aux - by biblatex package
#   -blx.bib - by biblatex package
#   _ref.tex - by sortref
#   .bmc - by dviout
#   .pbm - by dviout
#   -eps-converted-to.pdf - by epstopdf
mostlycleanfiles = $(call cache,mostlycleanfiles_impl)

mostlycleanfiles_impl = $(wildcard $(strip \
	$(srctexfiles:.tex=.aux) \
	$(srctexfiles:.tex=.auxlock) \
	$(srctexfiles:.tex=.ax1) \
	$(srctexfiles:.tex=.ax2) \
	$(srctexfiles:.tex=.bbl) \
	$(srctexfiles:.tex=.bcf) \
	$(srctexfiles:.tex=.blg) \
	$(srctexfiles:.tex=.end) \
	$(srctexfiles:.tex=.fls) \
	$(srctexfiles:.tex=.fmt) \
	$(srctexfiles:.tex=.glg) \
	$(srctexfiles:.tex=.glo) \
	$(srctexfiles:.tex=.gls) \
	$(srctexfiles:.tex=.glsdefs) \
	$(srctexfiles:.tex=.glstex) \
	$(srctexfiles:.tex=.idx) \
	$(srctexfiles:.tex=.ilg) \
	$(srctexfiles:.tex=.ind) \
	$(srctexfiles:.tex=.ist) \
	$(srctexfiles:.tex=.lof) \
	$(srctexfiles:.tex=.log) \
	$(srctexfiles:.tex=.lot) \
	$(srctexfiles:.tex=.nav) \
	$(srctexfiles:.tex=.out) \
	$(srctexfiles:.tex=.run.xml) \
	$(srctexfiles:.tex=.snm) \
	$(srctexfiles:.tex=.spl) \
	$(srctexfiles:.tex=.synctex) \
	$(srctexfiles:.tex=.synctex.gz) \
	$(srctexfiles:.tex=.toc) \
	$(srctexfiles:.tex=.*.vrb) \
	$(srctexfiles:.tex=.xdy) \
	$(srctexfiles:.tex=Notes.bib) \
	$(srctexfiles:.tex=*-blx.aux) \
	$(srctexfiles:.tex=*-blx.bbl) \
	$(srctexfiles:.tex=*-blx.blg) \
	$(srctexfiles:.tex=-blx.bib) \
	$(srctexfiles:.tex=_ref.tex) \
	$(srcltxfiles:.ltx=.log) \
	*.bmc \
	*.pbm \
	*-convbkmk.ps \
	*-eps-converted-to.pdf \
	*.bb \
	*.xbb \
	*_tmp.??? \
	*/*-eps-converted-to.pdf \
	$(srctexfiles:.tex=-figure*.dpth) \
	$(srctexfiles:.tex=-figure*.log) \
	$(srctexfiles:.tex=-figure*.md5) \
	$(srctexfiles:.tex=-figure*.pdf) \
	$(srctexfiles:.tex=-diff.dvi) \
	$(srctexfiles:.tex=-diff.ps) \
	$(srctexfiles:.tex=-diff.pdf) \
	$(MOSTLYCLEANFILES) \
))

# $(cleanfiles) gives all generated files to be deleted by "make clean".
cleanfiles = $(call cache,cleanfiles_impl)

cleanfiles_impl = $(wildcard $(strip \
	$(srctexfiles:.tex=.tar.gz) \
	$(srctexfiles:.tex=.pdf) \
	$(srctexfiles:.tex=.ps) \
	$(srctexfiles:.tex=.eps) \
	$(srctexfiles:.tex=.dvi) \
	$(srctexfiles:.tex=.svg) \
	$(srctexfiles:.tex=.jpg) \
	$(srctexfiles:.tex=.png) \
	$(srcltxfiles:.ltx=.fmt) \
	$(srcdtxfiles:.dtx=.cls) \
	$(srcdtxfiles:.dtx=.sty) \
	$(CLEANFILES) \
	$(mostlycleanfiles) \
))

# $(color) gives the color mode in the output:
# - always
# - never
# - auto (default)
#
# Usually controlled via $(COLOR) given on the command line or
# in the user configuration files.
#
# For compatibility with previous versions:
# - fall back to $(MAKE_COLORS), if $(COLOR) is empty,
# - allow "none", which is translated to "never".
#
# NOTE: use of MAKE_COLORS is deprecated. In future, MAKE_COLORS might be
# used for customizing colorings, like LS_COLORS or GCC_COLORS.
#
color = $(call cache,color_impl)
color_impl = $(strip \
	$(if $(_get_color), \
		$(if $(or \
			$(findstring always,$(_get_color)), \
			$(findstring never,$(_get_color)), \
			$(findstring auto,$(_get_color)) \
		), \
			$(_get_color) \
		,$(if $(findstring none,$(_get_color)), \
			never \
		, \
			$(warning unrecognized COLOR=$(_get_color)) \
			auto \
		)) \
	, \
		auto \
	) \
)
_get_color = $(if $(COLOR),$(COLOR),$(MAKE_COLORS))

# $(color_enabled) is a shell script snippet that returns the exit code 0 if
# coloring is enabled, otherwise returns a non-zero value.
color_enabled = \
	$(if $(findstring always,$(color)), \
		: \
	,$(if $(findstring never,$(color)), \
		false \
	, \
		[ -t 1 ] \
	))

# $(call colorize,COMMAND-WITH-COLOR,COMMAND-WITHOUT-COLOR) invokes the first
# command when coloring is enabled, otherwise invokes the second command.
colorize = \
	$(if $(findstring always,$(color)), \
		$1 \
	,$(if $(findstring never,$(color)), \
		$2 \
	, \
		if [ -t 1 ]; then \
			$1; \
		else \
			$2; \
		fi \
	))

# $(call notification_message,MESSAGE) prints a notification message.
notification_message = \
	$(call colorize, \
		printf "\033$(CL_NOTICE)$1\033$(CL_NORMAL)\n" >&2 \
	, \
		echo "$1" >&2 \
	)

# $(call warning_message,MESSAGE) prints a warning message.
warning_message = \
	$(call colorize, \
		printf "\033$(CL_WARN)Warning: $1\033$(CL_NORMAL)\n" >&2 \
	, \
		echo "Warning: $1" >&2 \
	)

# $(call error_message,MESSAGE) prints an error message.
error_message = \
	$(call colorize, \
		printf "\033$(CL_ERROR)Error: $1\033$(CL_NORMAL)\n" >&2 \
	, \
		echo "Error: $1" >&2 \
	)

# $(call set_title,TITLE) changes the window title. (Default: do nothing.)
set_title = :

# $(call exec,COMMAND) invokes the command with checking the exit status.
# $(call exec,COMMAND,false) invokes the command but skips the check.
# $(call exec,COMMAND,,COLOR_FILTER) and $(call exec,COMMAND,false,COLOR_FILTER)
# use COLOR_FILTER for the stdout.
exec = \
	$(if $(and $(findstring not found,$1),$(findstring exit 1,$1)), \
		$1 \
	, \
		failed=false; \
		$(call colorize, \
			printf "\033$(CL_NOTICE)$1\033$(CL_NORMAL)\n"; \
			exec 3>&1; \
			pipe_status=`{ { $1 3>&- 4>&-; echo $$? 1>&4; } | \
					$(call colorize_output,$3) >&3; } 4>&1`; \
			exec 3>&-; \
			[ "$$pipe_status" = 0 ] || failed=: \
		, \
			echo "$1"; \
			$1 || failed=: \
		) \
		$(if $2,,; $(check_failed)) \
	)

# $(check_failed)
check_failed = $$failed && { [ -n "$$dont_delete_on_failure" ] || rm -f $@; exit 1; }; :

# $(colorize_output) gives sed commands for colorful output.
# $(colorize_output,COLOR_FILTER) gives an application specific filter.
colorize_output = $(colorize_output_$1)

colorize_output_ = cat

# Errors for LaTeX:
#   "! ...": TeX
# Warnings for LaTeX:
#   "LaTeX Warning ...": \@latex@warning
#   "Package Warning ...": \PackageWarning or \PackageWarningNoLine
#   "Class Warning ...": \ClassWarning or \ClassWarningNoLine
#   "No file ...": \@input{filename}
#   "No pages of output.": TeX
#   "Underfull ...": TeX
#   "Overfull ...": TeX
#   "pdfTeX warning ...": pdfTeX
colorize_output_latex = \
	sed 's/^\(!.*\)/\$\$\x1b$(CL_ERROR)\1\$\$\x1b$(CL_NORMAL)/; \
	s/^\(LaTeX[^W]*Warning.*\|Package[^W]*Warning.*\|Class[^W]*Warning.*\|No file.*\|No pages of output.*\|Underfull.*\|Overfull.*\|.*pdfTeX warning.*\)/\$\$\x1b$(CL_WARN)\1\$\$\x1b$(CL_NORMAL)/'

# Errors for BibTeX:
#   "I couldn't open database file ..."
#   "I couldn't open file name ..."
#   "I found no database files---while reading file ..."
#   "I found no \bibstyle command---while reading file ..."
#   "I found no \citation commands---while reading file ..."
#   "Repeated entry--- ..."
# Warnings for BibTeX:
#   "Warning-- ..."
colorize_output_bibtex = \
	sed 's/^\(I couldn.t open database file.*\|I couldn.t open file name.*\|I found no database files---while reading file.*\|I found no .bibstyle command---while reading file.*\|I found no .citation commands---while reading file.*\|Repeated entry---.*\)/\$\$\x1b$(CL_ERROR)\1\$\$\x1b$(CL_NORMAL)/; \
	s/^\(Warning--.*\)/\$\$\x1b$(CL_WARN)\1\$\$\x1b$(CL_NORMAL)/'

# Errors for ChkTeX:
#   "Error ... in ... line ...:"
# Warnings for ChkTeX:
#   "Warning ... in ... line ...:"
colorize_output_chktex = \
	sed 's/^\(Error .* in.* line.*:.*\)/\$\$\x1b$(CL_ERROR)\1\$\$\x1b$(CL_NORMAL)/; \
	s/^\(Warning .* in.* line.*:.*\)/\$\$\x1b$(CL_WARN)\1\$\$\x1b$(CL_NORMAL)/'

# For RedPen:
#   "...:...: ValidationError[...], ..."
colorize_output_redpen = \
	sed 's/^\(.*: ValidationError\[.*\]\)\(.*\)/\$\$\x1b$(CL_ERROR)\1\$\$\x1b$(CL_WARN)\2\$\$\x1b$(CL_NORMAL)/'

# $(call cmpver,VER1,OP,VER2) compares the given two version numbers.
cmpver = { \
	cmpver_ver1_="$1"; \
	cmpver_ver2_="$3"; \
	$(call cmpver_fmt_,cmpver_ver1_); \
	$(call cmpver_fmt_,cmpver_ver2_); \
	$(if $(filter -eq,$2), \
		[ $$cmpver_ver1_ = $$cmpver_ver2_ ]; \
	, \
		$(if $(filter -ne,$2), \
			[ $$cmpver_ver1_ != $$cmpver_ver2_ ]; \
		, \
			cmpver_small_=`{ echo $$cmpver_ver1_; echo $$cmpver_ver2_; } | sort | head -1`; \
			$(if $(filter -le,$2),[ $$cmpver_small_ = $$cmpver_ver1_ ];) \
			$(if $(filter -lt,$2),[ $$cmpver_small_ = $$cmpver_ver1_ ] && [ $$cmpver_ver1_ != $$cmpver_ver2_ ];) \
			$(if $(filter -ge,$2),[ $$cmpver_small_ = $$cmpver_ver2_ ];) \
			$(if $(filter -gt,$2),[ $$cmpver_small_ = $$cmpver_ver2_ ] && [ $$cmpver_ver1_ != $$cmpver_ver2_ ];) \
		) \
	) \
	}

# $(call cmpver_fmt_,VAR)
cmpver_fmt_ = \
	$1=`expr "$$$1" : '[^0-9]*\([0-9][0-9]*\(\.[0-9][0-9]*\)*\)' | sed 's/\./ /g'`; \
	$1=`printf '%05d' $$$1`

##

ifneq ($(subdirs),)

# $(call make_for_each_subdir,TARGET) invokes Make for the given target
# (if exists) in all subdirectories.
make_for_each_subdir = \
	for dir in $(subdirs); do \
		if $(MAKE) -n -C $$dir $1 >/dev/null 2>&1; then \
			$(MAKE) -C $$dir $1; \
		fi; \
	done

else

make_for_each_subdir = :

endif

##

ifeq ($(DIFF),)

all: $(target)

else

all: $(diff_target)

endif

all-recursive:
	@$(call make_for_each_subdir,all-recursive)
	@$(MAKE) all

help: export help_message1 = $(help_message)
help:
	@echo "$$help_message1"

dvi: $(target_basename:=.dvi)

ps: $(target_basename:=.ps)

eps: $(target_basename:=.eps)

svg: $(target_basename:=.svg)

jpg: $(target_basename:=.jpg)

png: $(target_basename:=.png)

pdf: $(target_basename:=.pdf)

dist: $(target_basename:=.tar.gz)

fmt: $(target_basename:=.fmt)

$(target_basename:=.dvi) \
$(target_basename:=.ps) \
$(target_basename:=.eps) \
$(target_basename:=.svg) \
$(target_basename:=.jpg) \
$(target_basename:=.png) \
$(target_basename:=.pdf): | prerequisite

prerequisite: _prerequisite
	@$(call make_for_each_subdir,$(PREREQUISITE_SUBDIRS))

mostlyclean:
	@$(call make_for_each_subdir,mostlyclean)
	@$(if $(mostlycleanfiles),$(call exec,rm -f $(mostlycleanfiles)))
	@$(if $(wildcard $(DEPDIR) $(DIFFDIR) $(BUILDDIR) $(MOSTLYCLEANDIRS)), \
		$(call exec,rm -rf $(wildcard $(DEPDIR) $(DIFFDIR) $(BUILDDIR) $(MOSTLYCLEANDIRS))) \
	)

clean:
	@$(call make_for_each_subdir,clean)
	@$(if $(cleanfiles),$(call exec,rm -f $(cleanfiles)))
	@$(if $(wildcard $(DEPDIR) $(DIFFDIR) $(BUILDDIR) $(MOSTLYCLEANDIRS) $(CLEANDIRS)), \
		$(call exec,rm -rf $(wildcard $(DEPDIR) $(DIFFDIR) $(BUILDDIR) $(MOSTLYCLEANDIRS) $(CLEANDIRS))) \
	)

lint:
	@lint_ok=:; \
	$(foreach lint,$(LINTS), \
		$(if $(wildcard $(lint)), \
			$(call _lint_run,./$(lint)) \
		,$(if $(and $(filter-out lint,$(lint)),$(call rule_exists,$(lint))), \
			$(call _lint_rule,$(lint)) \
		,$(if $(and $(filter-out lint,$(lint)),$(call rule_exists,_builtin_lint_$(lint))), \
			$(call _lint_builtin_rule,$(lint)) \
		, \
			$(call _lint_run,$(lint)) \
		))) \
	) \
	$$lint_ok

# $(call _lint_run,EXECUTABLE) runs EXECUTABLE.
_lint_run = \
	$(foreach texfile,$(wildcard *.tex), \
		$(call exec,$1 $(texfile),false); \
		$$failed && lint_ok=false; \
	)

# $(call _lint_rule,RULE) runs RULE.
_lint_rule = \
	$(foreach texfile,$(wildcard *.tex), \
		$(call colorize, \
			printf "\033$(CL_NOTICE)$(MAKE) $1 1=$(texfile)\033$(CL_NORMAL)\n" \
		, \
			echo "$(MAKE) $1 1=$(texfile) " \
		); \
		$(MAKE) --no-print-directory $1 1="$(texfile)" || lint_ok=false; \
	)

# $(call _lint_builtin_rule,RULE) runs the builtin RULE.
_lint_builtin_rule = \
	$(foreach texfile,$(wildcard *.tex), \
		$(MAKE) --no-print-directory _builtin_lint_$1 1=$(texfile) || lint_ok=false; \
	)

# Check common mistakes about spacing after periods (deprecated).
# NOTE: --color=always is not POSIX.
_builtin_lint_check_periods:
	@$(call colorize, \
		printf "\033$(CL_NOTICE)check_periods $1\033$(CL_NORMAL)\n" \
	, \
		echo "check_periods $1" \
	)
	@grep_opts=; \
	$(if $(has_gnu_grep), \
		if $(color_enabled); then \
			grep_opts=--color=always; \
		fi; \
	) \
	if grep -n $$grep_opts '[A-Z][A-Z][A-Z]*)\?\.' $1; then \
		$(call error_message,most likely wrong spacing after periods. You may need to insert \\@); \
		exit 1; \
	fi

_builtin_lint_chktex:
	@$(call exec,$(chktex) $1,,chktex)

_builtin_lint_aspell:
	@$(call colorize, \
		printf "\033$(CL_NOTICE)$(aspell) -a -t <$1\033$(CL_NORMAL)\n" \
	, \
		echo "$(aspell) -a -t <$1" \
	)
	@grep_expr=$$($(aspell) -a -t <"$1" | tail -n +2 | cut -d ' ' -f 2 | grep -v '*' | sed '/^$$/d' | sort | uniq | awk '{printf "-e %s ",$$0}'); \
	if [ -n "$$grep_expr" ]; then \
		grep_opts=; \
		$(if $(has_gnu_grep), \
			if $(color_enabled); then \
				grep_opts=--color=always; \
			fi; \
		) \
		grep -n $$grep_opts $$grep_expr "$1"; \
		exit 1; \
	fi

_builtin_lint_textlint:
	@if $(color_enabled); then \
		$(call exec,$(textlint) --color $1); \
	else \
		$(call exec,$(textlint) --no-color $1); \
	fi

_builtin_lint_redpen:
	@$(call exec,$(redpen) $1,,redpen)

check:
	@$(call make_for_each_subdir,check)
	@$(foreach test,$(TESTS), \
		$(if $(wildcard $(test)), \
			$(call _check_run,./$(test)) \
		,$(if $(and $(filter-out check,$(test)),$(call rule_exists,$(test))), \
			$(call _check_rule,$(test)) \
		, \
			$(call _check_run,$(test)) \
		)) \
	)

# $(call _check_run,EXECUTABLE) runs EXECUTABLE.
_check_run = \
	$(if $(TESTS_PARAMS), \
		$(foreach param,$(TESTS_PARAMS), \
			$(call exec,$1 $(call TESTS_OPT,$1,$(param)) $(param)); \
		) \
	, \
		$(call exec,$1 $(call TESTS_OPT,$1)); \
	)

# $(call _check_rule,RULE) runs RULE.
_check_rule = \
	$(if $(TESTS_PARAMS), \
		$(foreach param,$(TESTS_PARAMS), \
			$(call colorize, \
				printf "\033$(CL_NOTICE)$(MAKE) $1 1=\"$(call TESTS_OPT,$1,$(param)) $(param)\"\033$(CL_NORMAL)\n" \
			, \
				echo "$(MAKE) $1 1=\"$(call TESTS_OPT,$1,$(param)) $(param)\"" \
			); \
			$(MAKE) --no-print-directory $1 1="$(call TESTS_OPT,$1,$(param)) $(param)" || exit 1; \
		) \
	, \
		$(call colorize, \
			printf "\033$(CL_NOTICE)$(MAKE) $1 1=\"$(call TESTS_OPT,$1)\"\033$(CL_NORMAL)\n" \
		, \
			echo "$(MAKE) $1 1=\"$(call TESTS_OPT,$1)\"" \
		); \
		$(MAKE) --no-print-directory $1 1="$(call TESTS_OPT,$1)" || exit 1; \
	)

# The "watch" mode. Try to update .log files instead of .pdf/.dvi files,
# otherwise make would continuously try to typeset for sources previously
# failed.
#
# NOTE: making .log files requires BUILDDIR=$(BUILDDIR) because the pattern rule
# needs the value when the rule is defined (before including user configuration
# files).
watch:
	@$(init_toolchain)
	@if $(if $(srctexfiles:.tex=.$(default_target)),:,false); then \
		$(call set_title,watching); \
		if $(MAKE) -q -s $(srctexfiles:.tex=.$(default_target)); then :; else \
			$(call set_title,running); \
			if time $(MAKE) -s $(srctexfiles:.tex=.$(default_target)); then \
				$(call set_title,watching); \
			else \
				$(call set_title,failed); \
			fi; \
		fi; \
		$(ensure_build_dir); \
		touch $(addprefix $(build_prefix),$(srctexfiles:.tex=.log)); \
		$(print_watching_message); \
		while :; do \
			sleep 1; \
			if $(MAKE) -q -s BUILDDIR=$(BUILDDIR) $(addprefix $(build_prefix),$(srctexfiles:.tex=.log)); then :; else \
				$(call set_title,running); \
				if time $(MAKE) -s BUILDDIR=$(BUILDDIR) $(addprefix $(build_prefix),$(srctexfiles:.tex=.log)); then \
					$(call set_title,watching); \
				else \
					$(call set_title,failed); \
				fi; \
				$(print_watching_message); \
			fi; \
		done \
	else \
		echo "No files to watch"; \
	fi

print_watching_message = $(call colorize, \
	printf "Watching for $(srctexfiles:.tex=.$(default_target)). \033$(CL_NOTICE)Press Ctrl+C to quit\033$(CL_NORMAL)\n" \
, \
	echo "Watching for $(srctexfiles:.tex=.$(default_target)). Press Ctrl+C to quit" \
)

# Upgrade files in the setup. (Be careful!)
# Files to be upgraded must have a tag like
#
#   latest-raw-url: https://raw.githubusercontent.com/tueda/makefile4latex/master/Makefile
#
# When the current directory is a Git repository and doesn't have the .gitignore
# file, this target downloads that of the Makefile4LaTeX repository.
#
# If the Makefile with a fixed version is used, then we need to prevent the
# upgrade from replacing the versioned Makefile. In the current implementation,
# we stop upgrading files that have names ending with "Makefile", assuming they
# all must not be upgraded. For now, we ignore the case with a commit hash
# starting with "v", which usually means a version tag like "v0.3.2".
upgrade:
	@$(call make_for_each_subdir,upgrade)
	@for file in * .* $(_cached_Makefile); do \
		case "$$file" in \
			*.swp|*.tmp|*~) \
				continue \
				;; \
			*Makefile) \
				case "$(MAKEFILE4LATEX_REVISION)" in \
					v*) \
						continue \
						;; \
				esac; \
				case "$(MAKEFILE4LATEX_VERSION)" in \
					*-dev) \
						;; \
					*) \
						continue \
						;; \
				esac; \
				;; \
		esac; \
		if [ -f "$$file" ] && [ ! -L "$$file" ]; then \
			if grep -q 'latest-raw-url *: *.' "$$file" >/dev/null 2>&1; then \
				url=$$(grep 'latest-raw-url *: *.' "$$file" | head -1 | sed 's/.*latest-raw-url *: *//' | sed 's/ .*//'); \
				$(call upgrade,$$file,$$url); \
			fi \
		fi; \
	done
	@if [ -d .git ] && [ ! -f .gitignore ]; then \
		$(call upgrade,.gitignore,https://raw.githubusercontent.com/tueda/makefile4latex/master/.gitignore); \
	fi

# $(call upgrade,FILE,URL) tries to upgrade the given file.
upgrade = \
	$(download) "$1.tmp" "$2" && { \
		if diff -q "$1" "$1.tmp" >/dev/null 2>&1; then \
			$(call notification_message,$1 is up-to-date); \
			rm -f "$1.tmp"; \
		else \
			mv -v "$1.tmp" "$1"; \
			$(call notification_message,$1 is updated); \
		fi; \
		:; \
	}

_FORCE:

.PHONY : all all-recursive check clean dist dvi eps fmt help jpg lint mostlyclean pdf png ps prerequisite svg upgrade watch _FORCE

# $(call typeset,LATEX-COMMAND) tries to typeset the document.
# $(call typeset,LATEX-COMMAND,false) doesn't delete the output file on failure.
typeset = \
	rmfile=$@; \
	rmauxfile=; \
	rmtmpfile=; \
	$(if $2,rmfile=;dont_delete_on_failure=1;) \
	$(ensure_build_dir); \
	oldfile_prefix=$*.tmp$$$$; \
	trap 'rm -f $$rmfile $$rmauxfile $$rmtmpfile $(build_prefix)$$oldfile_prefix*' 0 1 2 3 15; \
	failed=false; \
	if [ -f '$@' ]; then \
		need_latex=$(if $(filter-out %.ref %.bib %.bst %.idx %.glo,$?),:,false); \
		need_bibtex=$(if $(filter %.bib %.bst,$?),:,false); \
		need_biber=$(if $(filter %.bcf,$?),:,false); \
		need_sortref=$(if $(filter %.ref,$?),:,false); \
		need_makeindex=$(if $(filter %.idx,$?),:,false); \
		need_makeglossaries=$(if $(filter %.glo,$?),:,false); \
		need_bib2gls=false; \
		need_axohelp=$(if $(filter %.ax2,$?),:,false); \
		if $$need_bibtex || $$need_biber || $$need_sortref; then \
			[ ! -f '$(build_prefix)$*.aux' ] && need_latex=:; \
		fi; \
	else \
		need_latex=:; \
		need_bibtex=false; \
		need_biber=false; \
		need_sortref=false; \
		need_makeindex=false; \
		need_makeglossaries=false; \
		need_bib2gls=false; \
		need_axohelp=false; \
	fi; \
	$(call do_latex,$1,false); \
	if $$failed && $(check_noreffile); then \
		need_sortref=:; \
		failed=false; \
	else \
		$(check_failed); \
	fi; \
	i=1; \
	while [ $$i -lt $(MAXREPEAT) ]; do \
		$(do_bibtex); \
		$(do_biber); \
		$(do_sortref); \
		$(do_makeindex); \
		$(do_makeglossaries); \
		$(do_bib2gls); \
		$(do_axohelp); \
		$(call do_latex,$1); \
		i=$$((i + 1)); \
	done; \
	if $$need_latex || $$need_bibtex || $$need_biber || $$need_sortref \
			|| $$need_makeindex || $$need_makeglossaries || $$need_bib2gls \
			|| $$need_axohelp; then \
		$(call warning_message,Typesetting did not finish after $(MAXREPEAT) iterations. The document may be incomplete.); \
	fi; \
	rmfile=; \
	touch $@; \
	$(call mk_fls_dep,$@,$(build_prefix)$*.fls); \
	$(call mk_blg_dep,$@,$(build_prefix)$*.blg); \
	$(check_reffile) && $(call mk_ref_dep,$@,$*.ref); \
	:

# $(ensure_build_dir) creates $(BUILDDIR) if necessary.
ensure_build_dir = $(if $(BUILDDIR),mkdir -p $(BUILDDIR),:)

# $(build_prefix) is "$(BUILDDIR)/" if BUILDDIR is given, otherwise empty.
build_prefix = $(if $(BUILDDIR),$(BUILDDIR)/,)

# $(mv_target) moves the target file from BUILDDIR if BUILDDIR is defined.
# It also ensures that the target file exists in the working directory.
# $(call mv_target,FILE) moves FILE, instead of the target file.
# $(call mv_target,FILE,false) doesn't ensure that the file exists in the
# working directory.
mv_target = $(strip \
	$(if $1, \
		$(if $(BUILDDIR), \
			if [ -f $(BUILDDIR)/$1 ]; then mv $(BUILDDIR)/$1 $1; fi \
			$(if $2,,; [ -f $1 ]) \
		, \
			$(if $2,:,[ -f $1 ]) \
		) \
	, \
		$(if $@, \
			$(call mv_target,$@,$2) \
		, \
			: \
		) \
	) \
)

# $(call do_backup,FILE) creates a backup file for "$(build_prefix)/FILE".
do_backup = \
	[ -f '$(build_prefix)$1' ] && cp '$(build_prefix)$1' "$(build_prefix)$$oldfile_prefix$(suffix $1)"

# $(call check_modified,FILE) checks if "$(build_prefix)/FILE" was modified
# in comparison with the backup file.
check_modified = \
	$(call check_modified_impl,"$(build_prefix)$$oldfile_prefix$(suffix $1)",'$(build_prefix)$1')

check_modified_impl = \
	if [ -f $1 ] || [ -f $2 ]; then \
		if diff -q -N $1 $2 >/dev/null 2>&1; then \
			false; \
		else \
			:; \
		fi; \
	else \
		false; \
	fi

# $(call set_aux_file,FILE) sets the current auxiliary file to
# "$(build_prefix)$/FILE", which will be deleted if the current task fails.
set_aux_file = \
	rmauxfile=$(build_prefix)$1

# $(reset_aux_file) resets the current auxiliary file.
reset_aux_file = \
	rmauxfile=

# $(call copy_build_temp_file,FILE) copies $(build_prefix)$/FILE to the current
# directory if exists.
copy_build_temp_file = \
	$(if $(BUILDDIR), \
		if [ -f $(BUILDDIR)/$1 ]; then \
			cp $(BUILDDIR)/$1 .; \
			rmtmpfile="$$rmtmpfile $1"; \
		fi \
	, \
		: \
	)

# $(clear_build_temp_files) deletes temporary files copied from BUILDDIR.
clear_build_temp_files = \
	$(if $(BUILDDIR), \
		rm -f $$rmtmpfile; \
		rmtmpfile= \
	, \
		: \
	)

# $(call do_latex,LATEX-COMMAND)
# $(call do_latex,LATEX-COMMAND,false) skips the check.
do_latex = \
	if $$need_latex; then \
		need_latex=false; \
		$(call do_backup,$*.aux); \
		$(call do_backup,$*.toc); \
		$(call do_backup,$*.lof); \
		$(call do_backup,$*.lot); \
		$(call do_backup,$*.idx); \
		$(call do_backup,$*.glo); \
		$(call do_backup,$*.glstex); \
		$(call do_backup,$*.ax1); \
		$(call exec,$1 $<,$2,latex); \
		if $(call check_modified,$*.aux); then \
			if $(check_biblatex); then \
				if $(check_biblatex_rerun_bibtex); then \
					need_bibtex=:; \
				elif $(check_biblatex_rerun_biber); then \
					need_biber=:; \
				fi; \
			elif $(check_bblfile); then \
				need_bibtex=:; \
			fi; \
			$(check_reffile) && need_sortref=:; \
			if $(check_glstexfile); then \
				need_bib2gls=:; \
			else \
				$(check_glsfile) && need_makeglossaries=:; \
			fi; \
		else \
			$(check_nobblfile) && need_bibtex=:; \
		fi; \
		if $(call check_modified,$*.idx); then \
			$(check_indfile) && need_makeindex=:; \
		fi; \
		if $(call check_modified,$*.glo); then \
			$(check_glsfile) && need_makeglossaries=:; \
		fi; \
		if $(call check_modified,$*.ax1); then \
			$(check_ax2file) && need_axohelp=:; \
		fi; \
		{ $(check_rerun) || $(call check_modified,$*.toc) || $(call check_modified,$*.lof) || $(call check_modified,$*.lot); } && need_latex=:; \
	fi

# $(do_bibtex)
# NOTE: when BUILDDIR is used, we run bibtex in the current directory with
# temporarily copied .aux and Notes.bib files.
do_bibtex = \
	if $$need_bibtex; then \
		need_bibtex=false; \
		$(call do_backup,$*.bbl); \
		$(call set_aux_file,$*.bbl); \
		$(if $(BUILDDIR), \
			$(call copy_build_temp_file,$*.aux); \
			$(call copy_build_temp_file,$*Notes.bib); \
			$(call copy_build_temp_file,$*-blx.bib); \
			for f in $(BUILDDIR)/$**-blx.aux; do \
				ff=$$(basename $$f); \
				$(call copy_build_temp_file,$$ff); \
			done; \
			$(call exec,$(bibtex) $*,,bibtex); \
			mv $*.bbl $*.blg $(BUILDDIR)/; \
			for f in $**-blx.aux; do \
				if [ -f $$f ]; then \
					ff=$$(basename $$f .aux); \
					$(call exec,$(bibtex) $$ff,,bibtex); \
					mv $$ff.bbl $$ff.blg $(BUILDDIR)/; \
				fi; \
			done; \
			$(clear_build_temp_files); \
		, \
			$(call exec,$(bibtex) $*,,bibtex); \
			for f in $**-blx.aux; do \
				if [ -f $$f ]; then \
					ff=$$(basename $$f .aux); \
					$(call exec,$(bibtex) $$ff,,bibtex); \
				fi; \
			done; \
		) \
		$(reset_aux_file); \
		$(call check_modified,$*.bbl) && need_latex=:; \
	fi

# $(do_biber)
do_biber = \
	if $$need_biber; then \
		need_biber=false; \
		$(call do_backup,$*.bbl); \
		rmauxfile=$(build_prefix)$*.bbl; \
		$(if $(BUILDDIR), \
			$(call exec,$(biber) --output-directory $(BUILDDIR) $*); \
		, \
			$(call exec,$(biber) $*); \
		) \
		rmauxfile=; \
		$(call check_modified,$*.bbl) && need_latex=:; \
	fi

# $(do_sortref)
# NOTE: though the sortref script doesn't require any restriction on 'ref-file',
# we only support main-doc.tex + main-doc.ref -> main-doc_ref.tex.
do_sortref = \
	if $$need_sortref; then \
		need_sortref=false; \
		$(call do_backup,$*_ref.tex); \
		$(if $(BUILDDIR), \
			$(call exec,$(sortref) $(BUILDDIR)/$* $*.ref); \
			cp $(BUILDDIR)/$*_ref.tex .; \
		, \
			$(call exec,$(sortref) $* $*.ref); \
		) \
		$(call check_modified,$*_ref.tex) && need_latex=:; \
	fi

# $(do_makeindex)
# NOTE: when BUILDDIR is used, we run makeindex in the current directory with
# the temporarily copied .idx file.
do_makeindex = \
	if $$need_makeindex; then \
		need_makeindex=false; \
		$(call do_backup,$*.ind); \
		$(call set_aux_file,$*.ind); \
		$(if $(BUILDDIR), \
			$(call copy_build_temp_file,$*.idx); \
			$(call exec,$(makeindex) $*); \
			mv $*.ind $*.ilg $(BUILDDIR)/; \
			$(clear_build_temp_files); \
		, \
			$(call exec,$(makeindex) $*); \
		) \
		$(reset_aux_file); \
		$(call check_modified,$*.ind) && need_latex=:; \
	fi

# $(do_makeglossaries)
do_makeglossaries = \
	if $$need_makeglossaries; then \
		need_makeglossaries=false; \
		$(call do_backup,$*.gls); \
		$(if $(BUILDDIR), \
			$(call exec,$(makeglossaries) -d $(BUILDDIR) $*) \
		, \
			$(call exec,$(makeglossaries) $*) \
		); \
		$(call check_modified,$*.gls) && need_latex=:; \
	fi

# $(do_bib2gls)
do_bib2gls = \
	if $$need_bib2gls; then \
		need_bib2gls=false; \
		$(call do_backup,$*.glstex); \
		$(call set_aux_file,$*.glstex); \
		$(if $(BUILDDIR), \
			$(call copy_build_temp_file,$*.aux); \
			$(call exec,$(bib2gls) $*); \
			mv $*.glg $*.glstex $(BUILDDIR)/; \
			$(clear_build_temp_files); \
		, \
			$(call exec,$(bib2gls) $*); \
		) \
		$(reset_aux_file); \
		$(call check_modified,$*.glstex) && need_latex=:; \
	fi

# $(do_axohelp)
do_axohelp = \
	if $$need_axohelp; then \
		need_axohelp=false; \
		$(call do_backup,$*.ax2); \
		$(call exec,$(axohelp) $(build_prefix)$*); \
		$(call check_modified,$*.ax2) && need_latex=:; \
	fi

# $(call do_kpsewhich,FULLPATH-DEST-VAR,FILE)
do_kpsewhich = \
	fullpath_kpsewhich_impl=`$(kpsewhich) "$2"`; \
	if [ -z "$$fullpath_kpsewhich_impl" ]; then \
		$(call error_message,$2 not found); \
		exit 1; \
	fi; \
	$1=$$fullpath_kpsewhich_impl

# $(call mk_fls_dep,TARGET,FLS-FILE) saves dependencies from a .fls file.
mk_fls_dep = \
	if [ -f '$2' ]; then \
		mkdir -p $(DEPDIR); \
		{ \
			for f in `grep INPUT '$2' | sed 's/INPUT *\(\.\/\)\?//' | sort | uniq`; do \
				case $$f in \
					*:*|/*) ;; \
					*.fmt|*.run.xml) ;; \
					*) \
						$(call dep_entry,$1,$$f); \
						;; \
				esac; \
			done; \
		} | sort >$(DEPDIR)/$1.fls.d; \
	fi

# $(call mk_blg_dep,TARGET,BLG-FILE) saves dependencies from a .blg file.
mk_blg_dep = \
	if [ -f '$2' ]; then \
		mkdir -p $(DEPDIR); \
		{ \
			for f in `{ grep 'Database file [^:]*:' '$2'; grep 'The style file:' '$2'; } | sed 's/[^:]*://'`; do \
				$(call dep_entry,$1,$$f); \
			done; \
		} | sort >$(DEPDIR)/$1.blg.d; \
	fi

# $(call mk_glg_dep,TARGET,GLG-FILE) saves dependencies from a .glg file.
# NOTE: currently not used. We need some trick to find which executable
# (bibtex or bib2gls, maybe both?) should be run when a .bib dependency is
# updated.
mk_glg_dep = \
	if [ -f '$2' ] && grep -q 'bib2gls' '$2'; then \
		mkdir -p $(DEPDIR); \
		{ \
			for f in $$(grep 'Reading .*\.bib' '$2' | sed 's/Reading *//'); do \
				$(call dep_entry,$1,$$f); \
			done; \
		} | sort >$(DEPDIR)/$1.glg.d; \
	fi

# $(call mk_ref_dep,TARGET,REF-FILE) saves dependencies from a .ref file.
mk_ref_dep = \
	if [ -f '$2' ]; then \
		mkdir -p $(DEPDIR); \
		$(call dep_entry,$1,$2) | sort >$(DEPDIR)/$1.ref.d; \
	fi

# $(call dep_entry,TARGET,DEPENDENCY) prints a dependency entry.
# NOTE: DEPENDENCY can be a shell variable.
dep_entry = \
	if [ -f "$2" ]; then \
		echo "$1 : \$$(wildcard $2)"; \
		echo "$(build_prefix)$(basename $1).log : \$$(wildcard $2)"; \
	fi

# $(call grep_lines,PATTERN,FILE) greps PATTERN and prints lines around matches
# without new line characters.
# NOTE: the grep -B NUM option is not in POSIX.
grep_lines = \
	grep -B 3 $1 $2 | tr -d '\n'

# NOTE: latex may fail due to a missing _ref.tex.
check_noreffile = $(call grep_lines,'_ref.tex','$(build_prefix)$*.log') | grep "File \`$*_ref.tex' not found" >/dev/null 2>&1

check_biblatex = grep 'Package: biblatex' '$(build_prefix)$*.log' >/dev/null 2>&1

check_biblatex_rerun_biber = grep 'Please (re)run Biber' '$(build_prefix)$*.log' >/dev/null 2>&1

check_biblatex_rerun_bibtex = grep 'Please (re)run BibTeX' '$(build_prefix)$*.log' >/dev/null 2>&1

check_bblfile = $(call grep_lines,'.bbl','$(build_prefix)$*.log') | grep '$*.bbl' >/dev/null 2>&1

check_nobblfile = $(call grep_lines,'.bbl','$(build_prefix)$*.log') | grep 'No file $*.bbl' >/dev/null 2>&1

check_reffile = $(call grep_lines,'_ref.tex','$(build_prefix)$*.log') | grep '$*_ref.tex' >/dev/null 2>&1

check_indfile = $(call grep_lines,'.ind','$(build_prefix)$*.log') | grep '$*.ind' >/dev/null 2>&1

check_glsfile = $(call grep_lines,'.gls','$(build_prefix)$*.log') | grep '$*.gls\.' >/dev/null 2>&1

check_glstexfile = $(call grep_lines,'.glstex','$(build_prefix)$*.log') | grep '$*.glstex' >/dev/null 2>&1

# axodraw2.sty uses primitive control sequences for reading .ax2 file, instead
# of \input, without writing any jobname.ax2 in the log file. So we look for
# jobname.ax1; if it is found in the log file, it means axodraw2.sty tries to
# read jobname.ax2.
check_ax2file = $(call grep_lines,'.ax1','$(build_prefix)$*.log') | grep '$*.ax1' >/dev/null 2>&1

check_rerun = grep 'Rerun\|Please rerun LaTeX' '$(build_prefix)$*.log' | grep -v 'Package: rerunfilecheck\|rerunfilecheck.sty' >/dev/null 2>&1

#NOTE: xelatex doesn't work with -output-format=dvi.

.tex.dvi:
	@$(init_toolchain)
	@$(call switch,$(typeset_mode), \
		dvips, \
			$(call typeset,$(latex)) && \
			$(mv_target), \
		dvips_convbkmk, \
			$(call typeset,$(latex)) && \
			$(mv_target), \
		dvipdf, \
			$(call typeset,$(latex)) && \
			$(mv_target), \
		pdflatex, \
			$(call typeset,$(latex) $(PDFLATEX_DVI_OPT)) && \
			$(mv_target), \
	)

.tex.ps:
	@$(init_toolchain)
	@$(call switch,$(typeset_mode), \
		dvips, \
			$(call typeset,$(latex)) && \
			$(call exec,$(dvips) $(build_prefix)$*.dvi), \
		dvips_convbkmk, \
			$(call typeset,$(latex)) && \
			$(call exec,$(dvips) $(build_prefix)$*.dvi -o $(build_prefix)$*.ps) && \
			$(call exec,$(convbkmk) $(build_prefix)$*.ps) && \
			mv $(build_prefix)$*-convbkmk.ps $*.ps, \
		dvipdf, \
			$(call typeset,$(latex)) && \
			$(call exec,$(dvips) $(build_prefix)$*.dvi), \
		pdflatex, \
			$(call typeset,$(latex) $(PDFLATEX_DVI_OPT)) && \
			$(call exec,$(dvips) $(build_prefix)$*.dvi), \
	)

.tex.pdf:
	@$(init_toolchain)
	@$(call switch,$(typeset_mode), \
		dvips, \
			$(call typeset,$(latex)) && \
			$(call exec,$(dvips) $(build_prefix)$*.dvi -o $(build_prefix)$*.ps) && \
			$(call exec,$(ps2pdf) $(build_prefix)$*.ps), \
		dvips_convbkmk, \
			$(call typeset,$(latex)) && \
			$(call exec,$(dvips) $(build_prefix)$*.dvi -o $(build_prefix)$*.ps) && \
			$(call exec,$(convbkmk) $(build_prefix)$*.ps) && \
			mv $(build_prefix)$*-convbkmk.ps $(build_prefix)$*.ps && \
			$(call exec,$(ps2pdf) $(build_prefix)$*.ps), \
		dvipdf, \
			$(call typeset,$(latex)) && \
			$(call exec,$(dvipdf) $(build_prefix)$*.dvi), \
		pdflatex, \
			$(call typeset,$(latex)) && \
			$(mv_target), \
	)

# This always updates the timestamp of the target (.log).
$(build_prefix)%.log : %.tex
	@$(MAKE) -s $*.$(default_target)
	@touch $@

.dvi.eps:
	@$(init_toolchain)
	@trap 'rm -f $*.tmp.ps $*.tmp.pdf' 0 1 2 3 15; \
	$(call exec,$(dvips) -o $*.tmp.ps $<); \
	$(call exec,$(gs) -sDEVICE=pdfwrite -dPDFSETTINGS=/prepress -dEPSCrop -o $*.tmp.pdf $*.tmp.ps); \
	if $(call cmpver,`$(gs) --version`,-lt,9.15); then \
		$(call exec,$(gs) -sDEVICE=epswrite -o $@ $*.tmp.pdf); \
	else \
		$(call exec,$(gs) -sDEVICE=eps2write -o $@ $*.tmp.pdf); \
	fi

.dvi.svg:
	@$(init_toolchain)
	@$(call exec,$(dvisvgm) $<)

.pdf.jpg:
	@$(init_toolchain)
	@$(call exec,$(pdftoppm) $(PDFTOPPM_JPG_OPT) $< $*)

.pdf.png:
	@$(init_toolchain)
	@$(call exec,$(pdftoppm) $(PDFTOPPM_PNG_OPT) $< $*)

# Experimental (TeXLive)
.ltx.fmt:
	@$(init_toolchain)
	@$(ensure_build_dir)
	@$(call exec,$(latex_noopt) -ini -jobname='$*' '&$(notdir $(basename $(latex_noopt))) $<\dump',,latex)
	@$(mv_target)
	@$(call exec,rm -f $*.pdf)

# Experimental (TeXLive)
#
# Example:
#   $ cat foo.tex
#   %&foo
#   \documentclass{beamer}
#   \begin{document}
#   \begin{frame}
#   Your presentation here.
#   \end{frame}
#   \end{document}
#   $ make clean
#   $ time make foo.pdf
#   $ make clean
#   $ time { make foo.fmt && make foo.pdf; }
#
# Note: axodraw2 checks if .ax2 file exists when loaded, which becomes a problem
#   if one includes it in a format file: whether or not .ax2 file exists is
#   stores in a format file.
#
.tex.fmt:
	@$(init_toolchain)
	@$(ensure_build_dir)
	@$(call exec,$(latex_noopt) -ini -jobname='$*' '&$(tex_format)' mylatexformat.ltx '$<',,latex)
	@$(mv_target)
	@$(call exec,rm -f $*.pdf)

.dtx.cls:
	@$(ensure_build_dir)
	@$(call exec,$(latex_noopt) $(basename $<).ins,,latex)
	@$(mv_target)

.dtx.sty:
	@$(ensure_build_dir)
	@$(call exec,$(latex_noopt) $(basename $<).ins,,latex)
	@$(mv_target)

.odt.pdf:
	@$(call exec,$(soffice) --headless --nologo --nofirststartwizard --convert-to pdf $<)

.jpg.bb:
	$(ebb) $<

.png.bb:
	$(ebb) $<

.pdf.bb:
	$(ebb) $<

.jpg.xbb:
	$(extractbb) $<

.png.xbb:
	$(extractbb) $<

.pdf.xbb:
	$(extractbb) $<

# A distribution (for arXiv) needs to include
# 1. The main tex file.
# 2. Files that the main tex file depends on, except
#    - files with absolute paths, which are considered as system files,
#    - files created by LaTeX during typesetting, e.g., *.aux files,
#    - *.ax2 file unless "\pdfoutput=1" is explicitly used.
#    This default behaviour may be overwritten by EXTRADISTFILES and
#    NODISTFILES. Note that .bbl, .ind, .gls files etc. should be included in
#    the distribution.
#    See https://arxiv.org/help/submit_tex#bibtex
# 3. "PoSlogo.pdf" without "\pdfoutput=1" most likely indicates that
#    "PoSLogo.ps" should be also included for the PoS class.
# 4. 00README.XXX file if exists, and
#    - Files listed in 00README.XXX with "ignore".
#    See https://arxiv.org/help/00README
# 5. Files listed in ANCILLARYFILES are included under a subdirectory "anc".
#    See https://arxiv.org/help/ancillary_files
%.tar.gz: %.$(default_target)
	@tmpdir=tmp$$$$; \
	mkdir $$tmpdir || exit 1; \
	$(if $(KEEP_TEMP),,trap 'rm -rf $$tmpdir' 0 1 2 3 15;) \
	pdfoutput=false; \
	if head -5 "$*.tex" | sed 's/%.*//' | grep -q '\pdfoutput=1'; then \
		pdfoutput=:; \
	fi; \
	if [ ! -f '$(build_prefix)$*.fls' ]; then \
		$(call error_message,$(build_prefix)$*.fls not found. Delete $*.$(default_target) and then retry); \
		exit 1; \
	fi; \
	dep_files=; \
	for f in `grep INPUT '$(build_prefix)$*.fls' | sed 's/^INPUT *//' | sed '/^kpsewhich/d' | sed 's|^\.\/||' | sort | uniq`; do \
		case $$f in \
			*:*|/*|*.aux|*.lof|*.lot|*.nav|*.out|*.spl|*.toc|*.vrb|*-eps-converted-to.pdf|*.run.xml) ;; \
			*) \
				case $$f in \
					*.ax2) \
						$$pdfoutput || continue; \
						;; \
					PoSlogo.pdf) \
						if $$pdfoutput; then :; else \
							if [ -f PoSlogo.ps ]; then \
								$(call add_dist,PoSlogo.ps,$$tmpdir,dep_files); \
							fi; \
						fi; \
						;; \
				esac; \
				$(call add_dist,$$f,$$tmpdir,dep_files); \
		esac; \
	done; \
	for ff in $(EXTRADISTFILES); do \
		$(call do_kpsewhich,f,$$ff); \
		cp "$$f" "$$tmpdir/" || exit 1; \
		dep_files="$$dep_files $$f"; \
	done; \
	if [ -f 00README.XXX ]; then \
		cp "00README.XXX" "$$tmpdir/" || exit 1; \
		dep_files="$$dep_files 00README.XXX"; \
		for f in `grep ignore 00README.XXX | sed 's/ *ignore *$$//'`; do \
			cp --parents "$$f" "$$tmpdir/" || rsync -R "$$f" "$$tmpdir" || exit 1; \
			dep_files="$$dep_files $$f"; \
		done; \
	fi; \
	for f in $(ANCILLARYFILES); do \
		[ -d "$$tmpdir/anc" ] || mkdir "$$tmpdir/anc"; \
		cp "$$f" "$$tmpdir/anc/" || exit 1; \
		dep_files="$$dep_files $$f"; \
	done; \
	mkdir -p $(DEPDIR); \
	{ \
		for f in $$dep_files; do \
			echo "$@ : \$$(wildcard $$f)"; \
		done; \
	} >$(DEPDIR)/$@.d; \
	cd $$tmpdir || exit 1; \
	$(call exec,tar cfv - --exclude $@ * | gzip -9 -n >$@,false); \
	cd .. || exit 1; \
	$(check_failed); \
	mv $$tmpdir/$@ $@

# $(call add_dist,FILE,TMPDIR,DEP_FILES_VAR) copies FILE to TMPDIR and add it to
# DEP_FILES_VAR, if it is not in NODISTFILES.
add_dist = { \
		tmp_ok=:; \
		for tmp_ff in $(NODISTFILES); do \
			if [ "x$1" = "x$$tmp_ff" ]; then \
				tmp_ok=false; \
				break; \
			fi; \
		done; \
		if $$tmp_ok; then \
			tmp_d=`dirname "$1"`; \
			$(if $(BUILDDIR), \
				if [ "$$tmp_d" = "$(BUILDDIR)" ]; then \
					tmp_d=.; \
				fi; \
			) \
			mkdir -p "$2/$$tmp_d"; \
			cp "$1" "$2/$$tmp_d" || exit 1; \
			$3="$$$3 $1"; \
		fi; \
		:; \
	}

ifneq ($(DIFF),)

# Take a LaTeX-diff of two Git revisions (or a Git revision and the current
# working copy) given in the DIFF variable and typeset the resultant document.
# Limitation: though DIFF=rev1..rev2 is supported, the original LaTeX source
# file needs to exist as long as we want to use the rule *.tex -> *-diff.*.
%-diff.$(default_target): %.tex _FORCE
	@$(call get_rev,$(DIFF),_rev1,_rev2); \
	if [ -n "$$_rev1" ]; then \
		if git show "$$_rev1:./$<" >/dev/null 2>&1; then :; else \
			$(call error_message,$< not in $$_rev1); \
			exit 1; \
		fi; \
	fi; \
	if [ -n "$$_rev2" ]; then \
		if git show "$$_rev2:./$<" >/dev/null 2>&1; then :; else \
			$(call error_message,$< not in $$_rev2); \
			exit 1; \
		fi; \
	fi; \
	_tmpdir=tmp$$$$; \
	$(if $(KEEP_TEMP),,trap 'rm -rf $$_tmpdir' 0 1 2 3 15;) \
	_git_root=$$(git rev-parse --show-cdup).; \
	_git_prefix=$$(git rev-parse --show-prefix); \
	if [ -z "$$_rev2" ]; then \
		$(call expand_latexdiff_repo,$$_rev1); \
		$(MAKE) -f $(Makefile) $*.tar.gz || exit 1; \
		mkdir $$_tmpdir; \
		(cd $$_tmpdir && tar xfz ../$(DIFFDIR)/$$_rev1/$$_git_prefix/$*.tar.gz); \
		(cd $$_tmpdir && tar xfz ../$*.tar.gz); \
		$(call latexdiff_copy_cache,$(DIFFDIR)/$$_rev1/$$_git_prefix,$$_tmpdir); \
		$(call latexdiff_copy_cache,.,$$_tmpdir); \
		cp $(DIFFDIR)/$$_rev1/$$_git_prefix/$*-expanded.tex $$_tmpdir/$*-expanded-old.tex; \
		$(call expand_latex_source,$<,$$_tmpdir/$*-expanded-new.tex); \
		$(call latexdiff_insubdir,$$_tmpdir,$<,$*-expanded-old.tex,$*-expanded-new.tex,$*-diff.tex,$*-diff.$(default_target),$(DIFF)..); \
	else \
		$(call expand_latexdiff_repo,$$_rev1); \
		$(call expand_latexdiff_repo,$$_rev2); \
		mkdir $$_tmpdir; \
		(cd $$_tmpdir && tar xfz ../$(DIFFDIR)/$$_rev1/$$_git_prefix/$*.tar.gz); \
		(cd $$_tmpdir && tar xfz ../$(DIFFDIR)/$$_rev2/$$_git_prefix/$*.tar.gz); \
		$(call latexdiff_copy_cache,$(DIFFDIR)/$$_rev1/$$_git_prefix,$$_tmpdir); \
		$(call latexdiff_copy_cache,$(DIFFDIR)/$$_rev2/$$_git_prefix,$$_tmpdir); \
		cp $(DIFFDIR)/$$_rev1/$$_git_prefix/$*-expanded.tex $$_tmpdir/$*-expanded-old.tex; \
		cp $(DIFFDIR)/$$_rev2/$$_git_prefix/$*-expanded.tex $$_tmpdir/$*-expanded-new.tex; \
		$(call latexdiff_insubdir,$$_tmpdir,$<,$*-expanded-old.tex,$*-expanded-new.tex,$*-diff.tex,$*-diff.$(default_target),$(DIFF)); \
	fi

# $(call latexdiff_copy_cache,SOURCE-DIRECTORY,DESTINATION-DIRECTORY) copies
# cache files (i.e., eps-to-pdf) used in typesetting.
latexdiff_copy_cache = \
	for _f in $$(find "$2" -name '*.eps'); do \
		_ff="$1/$$(basename "$$_f" .eps)-eps-converted-to.pdf"; \
		if [ -f "$$_ff" ]; then \
			cp "$$_ff" $$(dirname "$$_f"); \
		fi; \
	done

# $(call expand_latexdiff_repo,REVISION)
# Uses: $*, $$_git_root, $$_git_prefix
expand_latexdiff_repo = \
	mkdir -p $(DIFFDIR); \
	if [ -d $(DIFFDIR)/$1 ]; then \
		git -C $(DIFFDIR)/$1 fetch origin; \
		case $1 in \
			*HEAD*) \
				git -C $(DIFFDIR)/$1 reset --hard origin/$1; \
				;; \
			*) \
				git -C $(DIFFDIR)/$1 reset --hard $1; \
				;; \
		esac; \
	else \
		git clone $$_git_root $(DIFFDIR)/$1; \
		git -C $(DIFFDIR)/$1 checkout $1; \
	fi; \
	rm -f $(DIFFDIR)/$1/$$_git_prefix/$(Makefile); \
	cp $(Makefile) $(DIFFDIR)/$1/$$_git_prefix/$(Makefile); \
	$(MAKE) -C $(DIFFDIR)/$1/$$_git_prefix -f $(Makefile) $*.tar.gz || exit 1; \
	case $1 in \
		*HEAD*) \
			rm -f $(DIFFDIR)/$1/$$_git_prefix/$*-expanded.tex; \
			;; \
	esac; \
	(cd $(DIFFDIR)/$1/$$_git_prefix && $(call expand_latex_source,$*.tex,$*-expanded.tex))

# $(call expand_latex_source,IN-TEX-FILE,OUT-TEX-FILE) expands a LaTeX source.
# Optionally a .bbl file is also expanded if exists.
expand_latex_source = { \
	if [ -f "$2" ]; then :; else \
		_tmp_latexexpand_fbody="$1"; \
		_tmp_latexexpand_fbody=$${_tmp_latexexpand_fbody%.*}; \
		$(if $(BUILDDIR), \
			if [ -f "$(BUILDDIR)/$$_tmp_latexexpand_fbody.bbl" ]; then \
				_tmp_latexexpand_fbody="$(BUILDDIR)/$$_tmp_latexexpand_fbody"; \
			fi; \
		) \
		if [ -f "$$_tmp_latexexpand_fbody.bbl" ]; then \
			if head "$$_tmp_latexexpand_fbody.bbl" | grep -q biber; then \
				$(call exec,$(latexpand) --biber "$$_tmp_latexexpand_fbody.bbl" "$1" >"$2.tmp"); \
			else \
				$(call exec,$(latexpand) --expand-bbl "$$_tmp_latexexpand_fbody.bbl" "$1" >"$2.tmp"); \
			fi; \
		else \
			$(call exec,$(latexpand) "$1" >"$2.tmp"); \
		fi; \
		mv "$2.tmp" "$2"; \
	fi \
}

# $(call latexdiff_insubdir,DIRECTORY,ORIG-TEX-FILE,OLD-TEX-FILE,NEW-TEX-FILE,TEMP-DIFF-TEX-FILE,TARGET-FILE,REVISIONS)
# performs latexdiff and then make for the target-diff file.
# When --math-markup=N is not given in LATEXDIFF_OPT, this code repeats
# the process with decreasing --math-markup from 3 to 0 until it succeeds.
# Similarly it also tries --allow-spaces if not given.
latexdiff_insubdir = \
	rm -f $1/$2; \
	cp $(Makefile) $1/$(Makefile); \
	[ -f .latex.mk ] && cp .latex.mk $1/; \
	[ -f latex.mk ] && cp latex.mk $1/; \
	$(if $(findstring --math-markup=,$(LATEXDIFF_OPT)), \
		$(if $(findstring --allow-spaces,$(LATEXDIFF_OPT)), \
			$(call latexdiff_insubdir_none,$1,$2,$3,$4,$5,$6,$7) \
		, \
			$(call latexdiff_insubdir_spaces,$1,$2,$3,$4,$5,$6,$7) \
		) \
	, \
		$(if $(findstring --allow-spaces,$(LATEXDIFF_OPT)), \
			$(call latexdiff_insubdir_math,$1,$2,$3,$4,$5,$6,$7) \
		, \
			$(call latexdiff_insubdir_math_spaces,$1,$2,$3,$4,$5,$6,$7) \
		) \
	) \
	mv $1/$6 .; \
	if [ -f "$6" ]; then \
		$(call notification_message,$6 generated for $7); \
	else \
		exit 1; \
	fi

latexdiff_insubdir_none = \
	(cd $1 && $(call exec,$(latexdiff) $3 $4 >$5)) || exit 1; \
	$(MAKE) -C $1 -f $(Makefile) $6 || exit 1;

latexdiff_insubdir_spaces = \
	(cd $1 && $(call exec,$(latexdiff) $3 $4 >$5)) || exit 1; \
	if $(MAKE) -C $1 -f $(Makefile) $6; then :; else \
		(cd $1 && $(call exec,$(latexdiff) --allow-spaces $3 $4 >$5)) || exit 1; \
		$(MAKE) -C $1 -f $(Makefile) $6 || exit 1; \
	fi;

latexdiff_insubdir_math = \
	(cd $1 && $(call exec,$(latexdiff) --math-markup=3 $3 $4 >$5)) || exit 1; \
	if $(MAKE) -C $1 -f $(Makefile) $6; then :; else \
		(cd $1 && $(call exec,$(latexdiff) --math-markup=2 $3 $4 >$5)) || exit 1; \
		if $(MAKE) -C $1 -f $(Makefile) $6; then :; else \
			(cd $1 && $(call exec,$(latexdiff) --math-markup=1 $3 $4 >$5)) || exit 1; \
			if $(MAKE) -C $1 -f $(Makefile) $6; then :; else \
				(cd $1 && $(call exec,$(latexdiff) --math-markup=0 $3 $4 >$5)) || exit 1; \
				$(MAKE) -C $1 -f $(Makefile) $6 || exit 1; \
			fi; \
		fi; \
	fi;

latexdiff_insubdir_math_spaces = \
	(cd $1 && $(call exec,$(latexdiff) --math-markup=3 $3 $4 >$5)) || exit 1; \
	if $(MAKE) -C $1 -f $(Makefile) $6; then :; else \
		(cd $1 && $(call exec,$(latexdiff) --math-markup=2 $3 $4 >$5)) || exit 1; \
		if $(MAKE) -C $1 -f $(Makefile) $6; then :; else \
			(cd $1 && $(call exec,$(latexdiff) --math-markup=1 $3 $4 >$5)) || exit 1; \
			if $(MAKE) -C $1 -f $(Makefile) $6; then :; else \
				(cd $1 && $(call exec,$(latexdiff) --math-markup=0 $3 $4 >$5)) || exit 1; \
				if $(MAKE) -C $1 -f $(Makefile) $6; then :; else \
					(cd $1 && $(call exec,$(latexdiff) --math-markup=3 --allow-spaces $3 $4 >$5)) || exit 1; \
					if $(MAKE) -C $1 -f $(Makefile) $6; then :; else \
						(cd $1 && $(call exec,$(latexdiff) --math-markup=2 --allow-spaces $3 $4 >$5)) || exit 1; \
						if $(MAKE) -C $1 -f $(Makefile) $6; then :; else \
							(cd $1 && $(call exec,$(latexdiff) --math-markup=1 --allow-spaces $3 $4 >$5)) || exit 1; \
							if $(MAKE) -C $1 -f $(Makefile) $6; then :; else \
								(cd $1 && $(call exec,$(latexdiff) --math-markup=0 --allow-spaces $3 $4 >$5)) || exit 1; \
								$(MAKE) -C $1 -f $(Makefile) $6 || exit 1; \
							fi; \
						fi; \
					fi; \
				fi; \
			fi; \
		fi; \
	fi;

endif

-include $(DEPDIR)/*.d
-include ~/.latex.mk
-include ~/latex.mk
-include .latex.mk
-include latex.mk

_prerequisite: $(PREREQUISITE)

.PHONY: _prerequisite
