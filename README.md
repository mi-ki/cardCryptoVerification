# Card-based Cryptography Meets Formal Verification
This program introduces (computer-aided) formal verification to card-based cryptography by providing a technique which automatically finds new protocols using as few as possible operations and searches for lowest bounds on card-minimal protocols.

More details are explained in the corresponding [paper](https://formal.iti.kit.edu/biblio/?lang=en&key=KochSchremppKirsten2019).

The entry point should be the script [``run.sh``](run.sh) which requires the bounded model checking tool [CBMC](http://www.cprover.org/cbmc/) (must be installed on your system or in the same folder).

Furthermore, you must specify the bounds for the desired protocol length.
Assuming you choose the number **_n_**, you would type the following in your shell:

```
./run.sh n
```

For more information, please contact [Michael Kirsten](https://formal.iti.kit.edu/~kirsten/?lang=en)
or [Alexander Koch](https://crypto.iti.kit.edu/index.php?id=akoch&L=2).
