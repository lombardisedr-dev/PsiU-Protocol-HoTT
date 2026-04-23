# Certified PSIU Protocol - SemiSimplicial Types (SST)

[![PSIU-Protocol-Final-Verification](https://github.com/lombardisedr-dev/PsiU-Protocol-HoTT/actions/workflows/agda-check.yml/badge.svg)](https://github.com/lombardisedr-dev/PsiU-Protocol-HoTT/actions/workflows/agda-check.yml)

Questo repository contiene la formalizzazione in **Agda** del protocollo PSIU, risolvendo il problema della coerenza nei tipi semisimpliciali (SST) fino alla dimensione $X_4$.

##  Certificazione Formale
Il progetto è validato tramite **GitHub Actions** con i seguenti parametri rigorosi:
- `--without-K`: Garantisce la compatibilità con la **Homotopy Type Theory (HoTT)**.
- `--safe`: Assicura l'assenza totale di postulati o assiomi non dimostrati.
- **Purely Constructive**: Tutte le prove di coerenza (dai triangoli $X_2$ ai pentatopi $X_4$) sono risolte tramite pattern matching su `refl`.

##  Struttura della Dimostrazione
1. **X₀ - X₁**: Definizione di punti e percorsi (Identity Types).
2. **X₂ (Triangoli)**: Coerenza della composizione dei cammini (`trans`).
3. **X₃ (Tetraedri)**: Chiusura volumetrica delle facce triangolari.
4. **X₄ (Pentatopi)**: Iper-coerenza dimensionale tra i volumi.
5. **Omega Stability**: Preservazione induttiva della struttura per $n \to \infty$.

##  Verifica Locale
Per eseguire il controllo manualmente:
```bash
agda --no-libraries -i . --without-K --safe Certified_PSIU_Protocol.agda
```















