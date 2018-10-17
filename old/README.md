# simp-isar-mode

This is a very shitty Emacs mode for **basic** displaying and editing of
Isabelle files (.thy) the idea is to avoid opening a fully fledged
JEdit for trivial stuff.

I have no idea how any of this works, everything was scraped from
Proof General isar-mode. This is my first time "writing" an Emacs mode
, so contributions are higly encouraged.


## How to use

Add this to your .emacs file

```elisp
;; Add to load-path or just put it somewhere apropiated
(add-to-list 'load-path "~/path/to/simp-isar-mode")

(require 'isar-mode)
```

have fun!
