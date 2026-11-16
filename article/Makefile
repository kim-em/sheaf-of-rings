.PHONY: all check submission clean

all:
	./verso/build.sh

check:
	python3 check_links.py

submission: all
	python3 package.py

clean:
	rm -rf verso/_out
	rm -f note.aux note.log note.out
