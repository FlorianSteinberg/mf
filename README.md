mpf: a coq library for multivalued pfunctions. The only dependency is ssreflect. It was tested with version 1.7. and Coq version 8.8.

To install copy and paste to the user-contrib folder of your coq installation, run "coq_makefile -f _CoqProject -o Makefile" to generate a makefile, afterwards run make and your all set.

There are parts that use classical reasoning and Choice principles. These parts are not exported by the all_mpf file but have to be imported separately.
