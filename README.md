# Certified PSIU Protocol - SemiSimplicial Types (SST)

[![PSIU-Protocol-Final-Verification](https://github.com)](https://github.com)

## Overview
[![PSIU-Protocol-Final-Verification](https://github.com/lombardisedr-dev/PsiU-Protocol-HoTT/actions/workflows/agda-check.yml/badge.svg)](https://github.com/lombardisedr-dev/PsiU-Protocol-HoTT/actions/workflows/agda-check.yml)

This project provides a formal verification of the **PSIU Protocol** within the framework of SemiSimplicial Types (SST). It is implemented in **Agda** and specifically designed to solve the coherence problem in higher dimensions without relying on Axiom K.

##  Formal Verification Details
The implementation is certified with the following rigorous Agda options:
- `{-# OPTIONS --without-K --safe #-}`
- **No Postulates**: All proofs are purely constructive, utilizing the J-rule via pattern matching on `refl`.
- **Higher Dimensions**: Coherence is verified from $X_0$ (points) up to $X_4$ (pentatopes).

##  Core Structure
The protocol is defined by the following layers:
1. **X₀ - X₁**: Points and Path-based edges.
2. **X₂**: Triangular face coherence (Path composition).
3. **X₃**: Tetrahedral volume coherence.
4. **X₄**: Pentatope hyper-volume coherence.
5. **Omega Stability**: Ensuring the structure remains "crystallized" through induction.

##  Usage
To verify the formal proof locally, ensure you have Agda 2.6.4+ installed and run:
```bash
agda --no-libraries -i . --without-K --safe Certified_PSIU_Protocol.agda
```














