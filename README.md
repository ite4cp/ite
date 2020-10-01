# ITE - Constructive Disjunction for Constraint Programming in SICStus Prolog
A lightweight approach for implementing constructive disjunction in Prolog.
The implementation has been described in the paper *ITE: A Lightweight Implementation of Stratified Reasoning for Constructive Logical Operators* (published in the [International Journal on Artificial Intelligence Tools](https://doi.org/10.1142/S0218213020600064)). A preprint of the paper is [available on arXiv](https://arxiv.org/abs/1811.03906).

## Summary
Constraint Programming (CP) is a powerful declarative programming paradigm combining inference and search in order to find solutions to various type of constraint systems. 
Dealing with highly disjunctive constraint systems is notoriously difficult in CP. 
Apart from trying to solve each disjunct independently from each other, there is little hope and effort to succeed in constructing intermediate results combining the knowledge originating from several disjuncts. 
In this paper, we propose If Then Else (ITE), a lightweight approach for implementing stratified constructive disjunction and negation on top of an existing CP solver, namely SICStus Prolog clp(FD).
Although constructive disjunction is known for more than three decades, it does not have straightforward implementations which go beyond local reasoning, in most CP solvers. 
Using a global constraint definition mechanism, ITE is a freely available library proposing stratified and constructive reasoning for various operators, including disjunction and negation, implication and conditional. 

## Usage examples
The file `ite.pl` contains the implementation of the ITE predicates. 

A typical example of using ITE:
```
Q: A in 1..5, B in 1..5, C in 1..5, (A-B #= 4) cd (B-A #= 4), (A-C #= 4) cd (C-A #=4)
A: A in{1}\/{5}, B in{1}\/{5}, C in{1}\/{5}
```

Additional examples can be found in `test_ite.pl`.

## Tests
A set of tests is available in `test_ite.pl`, implemented via the `plunit` interface.
They can be run as:
```
sicstus --nologo --noinfo -l test_ite.pl --goal "run_tests,halt." 
```

## Evaluation
A Jupyter notebook with scripts for evaluating ITE against the native clp(FD) constraints as well as the `smt` global constraint can be found in the subfolder `evaluation`.

## How to Cite

If ITE was useful for you, please cite one of the following publications

```
Gotlieb, A., Marijan, D., & Spieker, H. (2020). ITE: A Lightweight Implementation of Stratified Reasoning for Constructive Logical Operators. International Journal on Artificial Intelligence Tools, 29(03n04), 2060006. https://doi.org/10.1142/s0218213020600064 

Gotlieb, A., Marijan, D., & Spieker, H. (2018). Stratified Constructive Disjunction and Negation in Constraint Programming. 2018 IEEE 30th International Conference on Tools with Artificial Intelligence (ICTAI). 2018 IEEE 30th International Conference on Tools with Artificial Intelligence (ICTAI). https://doi.org/10.1109/ictai.2018.00026 
```

```
@article{Gotlieb2020,
  doi = {10.1142/s0218213020600064},
  url = {https://doi.org/10.1142/s0218213020600064},
  year = {2020},
  publisher = {World Scientific Pub Co Pte Lt},
  volume = {29},
  number = {03n04},
  pages = {2060006},
  author = {Arnaud Gotlieb and Dusica Marijan and Helge Spieker},
  title = {{ITE}: A Lightweight Implementation of Stratified Reasoning for Constructive Logical Operators},
  journal = {International Journal on Artificial Intelligence Tools}
}

@inproceedings{Gotlieb2018,
  doi = {10.1109/ictai.2018.00026},
  url = {https://doi.org/10.1109/ictai.2018.00026},
  year = {2018},
  month = nov,
  publisher = {{IEEE}},
  author = {Arnaud Gotlieb and Dusica Marijan and Helge Spieker},
  title = {Stratified Constructive Disjunction and Negation in Constraint Programming},
  booktitle = {2018 {IEEE} 30th International Conference on Tools with Artificial Intelligence ({ICTAI})}
}
```
