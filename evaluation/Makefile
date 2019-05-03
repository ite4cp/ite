constraints: constraints.pl ../ite.pl
	sicstus -f -l constraints.pl --goal "compile('constraints'), save_program('constraints.sav'), halt."
	spld --output constraints.exe --static constraints.sav

	chmod +x ./constraints.exe
	rm constraints.sav

.PHONY: clean

clean:
	rm constraints.exe

