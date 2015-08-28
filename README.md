# fNARS
Modular and fast (hopefully) implementation of NARS logic.

## Components diagram
![UML class diagram for fNARS components](http://www.yuml.me/64ae6de3 "UML class diagram for fNARS components")

"Inheritance" between NAL layers and NARS layers should be implemented with [final tagless](http://okmij.org/ftp/tagless-final/index.html) approach. [Here](https://oleksandrmanzyuk.wordpress.com/2014/06/18/from-object-algebras-to-finally-tagless-interpreters-2/) is good introduction to the approach from analogous OOP technique.

Likely that relationship between NAL and NARS could be implemented with final tagless too.
