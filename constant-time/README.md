# Verified Elimination of Secret Control-Flow

This the development accompanying our paper "Verified Elimination of Secret Control-Flow".

It contains a verified transform to remove secret-dependent control-flow.
It currently only works on a restricted subset of C, notably you cannot exit the main function, nor access memory, nor have loops.

We only support `x86_64` (mainly because safe operations are arch-specific), so compile and install via (inside CompCert main directory):
```
./configure x86_64-linux && make && make install
```

We tested our development with `coq 8.17.1` and `OCaml 4.14.1`.

----

To declare a parameter as secret, use the `tainted` attribute:

```c
__attribute((tainted(argc)))
int main(int argc, char** argv) {
  int x = 2;
  if (argc > x)
    return argc * argc - x;
  return 1;
}
```

Compiling the code with `-drtl` gives `code.rtl.*` files that contain the code after each RTL transform. In our case, `code.rtl.2` is the RTL before the transform and `code.rtl.3` the RTL afterwards. It is quite large because predication is applied to each instruction, but `code.rtl.9` should contain a lot of `nop`s after constant propagation and dead code elimination.

## Exiting Main

Without exiting main and accessing memory you cannot really do much.

If you replace every `CTTransform` with `CTTransformCheat` in `Compiler.v`, the transform is applied to every function except `main`, which allows you to do arbitrary stuff inside main.
Of course this breaks the semantic preservation proof.

```c
#include <stdio.h>
#include <stdlib.h>

__attribute((tainted(secret)))
int calc_secret(int secret, int ref, int i, int key[16]) {
  int x = key[i];
  int sbit = secret & 1;
  int rbit = ref & 1;
  if (rbit > sbit)
    return 0;
  if (ref > secret * i) {
    if (x == 0) return i;
    return i - ref;
  }
  return sbit;
}

int key[16] = {'j','e','s','u','s',' ','l','o','v','e','s',' ','y','o','u','!'};

int main(int argv, char** argc) {
  int res = 0;
  int secret = atoi(argc[1]);
  int public = atoi(argc[2]);
  
  for (int i=0; i<16; i++) {
    res += calc_secret(secret, public, i, key);
    secret >>= 1;
    public >>= 1;
  }
  
  return res;
}
```

In this example, `calc_secret` is linearized with respect to the `secret` parameter.
To better see how this linearization looks like, look at the `code.ct.*.calc_secret` files that also ppear with the `-drtl` option (only when using CTTransformCheat): they show the graph structure before and after linearization.

## Main Theorems

Our main theorems are:
- The semantic preservation proofs of our four transforms. `CTTransform.v` contains a bundled version of semantic preservation (`transl_program_correct`) for applying the four transforms consecutively.
- `Theorem control_flow_security` in `ControlFlowSecurity.v` proves that the transformed `PredRTL` code is free of secret control flow.
- `Corollary uni_chain_path` in `ControlFlowSecurity.v` is equivalent to Theorem 4.1 from Hack and Moll: it states that uniform program points can only be reached by live states.
  - `Theorem chain_containment` in `InfluenceRegion.v` is an important tool for proving the PCFL chain invariant and therefore `uni_chain_path`.
  - `Theorem uni_cdep_equivalent` in `TaintAnalysis.v` shows that our notion of uniform coincides with the one of Hack and Moll.
- `Theorem new_target_spec` and `Theorem new_target_chain` in `PCFLEdgeEmbedding.v` state two important properties of the PCFL algorithm about how a new target of an edge relates to its original target.
- Lemmata `taint_ana_params_spec`, `taint_ana_respects_reg_use_op`, `taint_ana_respects_ir` and `tainted_cond_spec` give the properties of our taint analysis which are required to prove control-flow security. These are Claims T0 through T3 of the Taint Analysis section in the paper.

