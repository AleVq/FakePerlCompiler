all:
	happy -gca -i ParPerl.y
	alex -g LexPerl.x
	ghc --make TestPerl.hs -o TestPerl

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi

distclean: clean
	-rm -f DocPerl.* LexPerl.* ParPerl.* LayoutPerl.* SkelPerl.* PrintPerl.* TestPerl.* AbsPerl.* TestPerl ErrM.* SharedString.* ComposOp.* Perl.dtd XMLPerl.* Makefile*
	
