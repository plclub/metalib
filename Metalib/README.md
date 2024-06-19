COMPILATION, INSTALLATION, AND DOCUMENTATION:

  This library requires Coq 8.15, available via [opam](https://opam.ocaml.org/)
  or from the Coq website [https://coq.inria.fr/download].

  To compile the library:

      `make`          generate Coq makefile, compile Coq files
      `make doc`      generate Coq documentation
      `make install`  install library on your system (locally)
  
  Note that both step 1 and 3 are needed in order to be able to run/compile
  the examples and the tutorial. In particular, step 3 only install the
  library in your local Coq setup, and does not require special privileges.
