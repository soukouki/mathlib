
all: Classical.vo Ensemble



%.vo: %.v
	coqc -Q . Local $<

Ensemble: Ensemble/Section1_1.vo Ensemble/Section1_2.vo Ensemble/Section1_3.vo Ensemble/Section1_4.vo Ensemble/Section1_5.vo

clean:
	find . -type f | grep -E "(.*\.vo)|(.*\.glob)|(.*\.aux)" - | xargs rm
