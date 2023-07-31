
all: Classical.vo Ensemble



%.vo: %.v
	coqc -Q . Local $<

Ensemble: Ensemble/Section1.vo Ensemble/Section2.vo Ensemble/Section3.vo Ensemble/Section4.vo

clean:
	find . -type f | grep -E "(.*\.vo)|(.*\.glob)|(.*\.aux)" - | xargs rm
