.PHONY : all coq html website clean

all: coq html website

html:
	$(MAKE) -C coq html

coq:
	$(MAKE) -C coq

website:
	$(MAKE) -C coq html
	mv coq/html/*html website
	rm -rf coq/html

clean:
	$(MAKE) -C coq clean
	rm -f website/*html
