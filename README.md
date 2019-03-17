mf: a coq library for multivalued functions. The only dependency is ssreflect. It was tested with version 1.7. and Coq version 8.8.2. It will probably not run with 8.9 due to the "masking of abslute name depreciated" warning, I'll provide compatability at some point.

To install copy and paste to any folder (best just clone the repository), then run "coq_makefile -f _CoqProject -o Makefile" to generate a makefile and afterwards run "make" and then "make install" and you're all set.

There are parts that use classical reasoning and choice principles. These parts are not exported by the all_mf file but have to be imported separately.
