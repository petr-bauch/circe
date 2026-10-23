# Circe report build (LuaLaTeX + biber; no latexmk required).
# Note: if luaotfload fails with "no writeable cache path" (e.g. sandboxed
# HOME), rerun with a writable cache, e.g.
#   TEXMFVAR=/tmp/texmf-var TEXMFCONFIG=/tmp/texmf-config make pdf
.PHONY: pdf status clean

pdf: status
	lualatex main.tex
	biber main
	lualatex main.tex
	lualatex main.tex

status:
	../../tools/report-status.sh

clean:
	rm -f main.pdf main.aux main.bbl main.bcf main.blg main.log main.out main.run.xml main.toc
	rm -rf build generated
