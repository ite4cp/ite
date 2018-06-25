# ITE - Constructive Disjunction for Constraint Programming in SICStus Prolog
A lightweight approach for implementing constructive disjunction in Prolog.
The implementation has been described in the paper *Stratified Constructive Disjunction and Negation in Constraint Programming*

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
