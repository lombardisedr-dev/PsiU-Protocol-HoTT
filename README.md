# PsiU-Protocol-HoTT

##  Certificazione di Validazione Formale

Il protocollo è stato verificato con successo utilizzando **Agda 2.6.4**.

### 1. Validazione Universale ($n = 10.000+$)
- **Stato**: ![Validato]
- **Descrizione**: Il protocollo è stato validato per ogni $n : \mathbb{N}$. La coerenza logica è garantita matematicamente per qualsiasi valore del parametro, inclusi carichi da 10.000 a 20.000 unità.



[![PSIU-Protocol-Final-Verification](https://github.com/lombardisedr-dev/PsiU-Protocol-HoTT/actions/workflows/agda-check.yml/badge.svg)](https://github.com/lombardisedr-dev/PsiU-Protocol-HoTT/actions/workflows/agda-check.yml)

Questo repository contiene la formalizzazione in **Agda** (Homotopy Type Theory) del protocollo PsiU...


### 2. Verifica Rigorosa (Safe Mode)
- **Stato**: ![No Postulates]
- **Requisiti superati**:
  - **Well-Typed**: Il codice è pienamente conforme al sistema dei tipi di Agda.
  - **No Postulates**: Non sono stati utilizzati assiomi non dimostrati (`postulate`). Ogni proprietà è stata derivata costruttivamente.
  - **Termination**: È garantito che ogni funzione del protocollo termini correttamente.

---
*Validazione eseguita automaticamente tramite [GitHub Actions]
[![PSIU-Protocol-Final-Verification](https://github.com/lombardisedr-dev/PsiU-Protocol-HoTT/actions/workflows/agda-check.yml/badge.svg)](https://github.com/lombardisedr-dev/PsiU-Protocol-HoTT/actions/workflows/agda-check.yml)















