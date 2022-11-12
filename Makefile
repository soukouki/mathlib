
all: Classical Ensembles

Classical: Classical.v
	coqc -Q . Local Classical.v

Ensembles: Ensembles.v
	coqc -Q . Local Ensembles.v

clean:
	find . -type f | grep -E "(.*\.vo)|(.*\.glob)|(.*\.aux)" - | xargs rm
