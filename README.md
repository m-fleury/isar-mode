# isar-mode

This is a very simple emacs mode for Isabelle (.thy) files. It provides only some syntax highlighting.



The intended use is in combination with ([LSP-isar](https://github.com/m-fleury/isabelle-release)).


# Installation

If you use quelpa
``elisp
:location (recipe
                             :fetcher github
                             :repo "m-fleury/isar-mode")
``

Otherwise clone the repo and add it to the load path.


# History

The mode started as a fork of ([simp-isar-mode](https://github.com/agomezl/simp-isar-mode)), but later changed as most of the syntax highlighting is provided by Isabelle's LSP server.
