# ITE - Evaluation Scripts

Scripts to run performance benchmarks on ITE.
Currently, two scripts are available:

## Sample Statements

Files: `SampleStatements.ipynb` + `benchmark.pl`

These scripts include the sample statements used for the experiments in our ICTAI 2018 paper.

## Global Constraint Implementations

Files: `GlobalConstraints.ipynb` + `constraints.pl`

These scripts include implementations of global constraints using ITE and regular clp(FD) operators.

To run the experiments, first create the `constraints.exe` by running `make`.
Running `constraints.exe` outputs the test results in CSV format to stdout and should be captured to a file.
Afterwards, the notebook can be run to create result plots.
