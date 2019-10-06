# cat

### A library for writing category theory proofs in Agda


Categories are implemented as interfaces (records in Agda).

Mostly broken. ~~Work in progress.~~ **UPDATE**: I'm using [agda-categories](https://github.com/agda/agda-categories/) instead!


The implementation of categories in this repository are actually *E-categories*, i.e., categories where morphisms are equipped with an equivalence relation. They arise rather naturally when implementing categories in a constructive framework like Agda. Some references and mentions of E-categories:
* [Constructive Category Theory](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.39.4193) by Huet and Saïbi 
* [Normalization and Yoneda embedding](https://pdfs.semanticscholar.org/dc4f/878e3ac58b60da0b0ab7f63443322bbc6518.pdf) by   Čubrić, Dybjer and Scott
* [A bicategorical analysis of E-categories](https://www.researchgate.net/publication/2710125_A_bicategorical_analysis_of_E-categories) by Kinoshita

Also checkout [JLimperg/cats](https://github.com/JLimperg/cats) if you want more advanced constructions.
