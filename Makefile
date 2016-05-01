all:
	happy -gca -i ParPerl.y
	alex -g LexPerl.x
	ghc --make TestPerl.hs -o TestPerl

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi

	
