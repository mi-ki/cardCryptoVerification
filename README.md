# Card-based Cryptography Meets Formal Verification
This program introduces (computer-aided) formal verification to card-based cryptography by providing a technique which automatically finds new protocols using as few as possible operations and searches for lowest bounds on card-minimal protocols.

More details are explained in the corresponding [paper](https://formal.iti.kit.edu/biblio/?lang=en&key=KochSchremppKirsten2019).

The entry point should be the script [``run.sh``](run.sh) which requires the bounded model checking tool [CBMC](http://www.cprover.org/cbmc/) (must be installed on your system or in the same folder).

Furthermore, you must specify the bound for the desired protocol length and the number of used cards.
Assuming you choose the number **_n_** for protocol length and **_c_** for the number of cards, you would type the following in your shell:

```
./run.sh c n
```

For more information, please contact [Michael Kirsten](https://formal.iti.kit.edu/~kirsten/?lang=en)
or [Alexander Koch](https://crypto.iti.kit.edu/index.php?id=akoch&L=2).

## Possible Configurations
The program is of a general nature such that different modes are supported. The most notable ones are accessible by the following parameters:

* **WEAK_SECURITY**: **0** denotes probabilistic security, **1** denotes input-possibilistic security, and **2** denotes output-possibilistic security.
* **FINITE_RUNTIME**: **1** denotes finite runtime, **0** denotes restart-free Las Vegas.
* **CLOSED_PROTOCOL**: **1** limits the search to closed protocols, i.e., only closed shuffles, **0** allows any shuffle operations.
* **FORCE_RANDOM_CUTS**: **1** limits the search to random cuts, **0** makes no restriction
* **MAX_PERM_SET_SIZE**: This variable is used to limit the permutation set in any shuffle to reduce the running time of the program. Note however that reducing this constant could exclude some valid protocols as some valid permutation sets might no longer be considered.

You can use the parameters by appending
```
'-D MODE PARAMETER'
```
for each of the options (**MODE** stands for the keyword and **PARAMETER** for the value).
