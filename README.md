# Card-Based Cryptography Meets Formal Verification
This program introduces (computer-aided) formal verification to card-based cryptography by providing a technique which automatically finds new protocols using as few as possible operations and searches for lowest bounds on card-minimal protocols.

More details are explained in the corresponding [paper](http://eprint.iacr.org/2019/1037).

## Getting Started
The entry point should be the script [``run.sh``](run.sh) which requires the bounded model checking tool [CBMC](http://www.cprover.org/cbmc/) (must be installed on your system or in the same folder).

Furthermore, you must specify the bound for the desired protocol length and the number of used cards.
Assuming you choose the number **_l_** for protocol length and **_n_** for the number of cards, you would type the following in your shell:

```
./run.sh n l
```

## Possible Configurations
The program is of a general nature such that different modes are supported. The most notable ones are accessible by the following parameters:

* **WEAK_SECURITY**: The value **0** denotes probabilistic security, **1** denotes input-possibilistic security, and **2** denotes output-possibilistic security.
* **FINITE_RUNTIME**: The value **1** denotes finite runtime, **0** denotes restart-free Las Vegas.
* **CLOSED_PROTOCOL**: The value **1** limits the search to closed protocols, i.e., only closed shuffles, **0** allows any shuffle operations.
* **FORCE_RANDOM_CUTS**: The value **1** limits the search to random cuts, **0** makes no restriction
* **MAX_PERM_SET_SIZE**: This variable is used to limit the permutation set in any shuffle to reduce the running time of the program. Note however that reducing this constant could exclude some valid protocols as some valid permutation sets might no longer be considered.

You can use the parameters by appending the following (do not omit the quotation marks) for each of the options (**MODE** stands for the keyword and **PARAMETER** for the value):

```
'-D MODE=PARAMETER'
```

## Example
For the experiments in the [paper](http://eprint.iacr.org/2019/1037), we used the configuration executed by the shell command

```
./run.sh 4 5 '-D WEAK_SECURITY=2' '-D MAX_PERM_SET_SIZE=8' '-D CLOSED_PROTOCOL=1'
```

for showing that no four-card protocol exists using five operations, as well as

```
./run.sh 4 6 '-D WEAK_SECURITY=2' '-D MAX_PERM_SET_SIZE=8' '-D CLOSED_PROTOCOL=1'
```

for constructing an output-possibilistic protocol using six operations.


## Contact
For more information, please contact [Michael Kirsten](https://formal.iti.kit.edu/~kirsten/?lang=en)
or [Alexander Koch](https://crypto.iti.kit.edu/index.php?id=akoch&L=2).
