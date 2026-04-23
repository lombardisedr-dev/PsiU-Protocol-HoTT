# PsiU-Protocol-HoTT

##  Certificazione di Validazione Formale

Il protocollo è stato verificato con successo utilizzando **Agda 2.6.4**.

### 1. Validazione Universale ($n = 10.000+$)
- **Stato**: ![Validato](https://shields.io)
- **Descrizione**: Il protocollo è stato validato per ogni $n : \mathbb{N}$. La coerenza logica è garantita matematicamente per qualsiasi valore del parametro, inclusi carichi da 10.000 a 20.000 unità.

### 2. Verifica Rigorosa (Safe Mode)
- **Stato**: ![No Postulates](https://shields.io)
- **Requisiti superati**:
  - **Well-Typed**: Il codice è pienamente conforme al sistema dei tipi di Agda.
  - **No Postulates**: Non sono stati utilizzati assiomi non dimostrati (`postulate`). Ogni proprietà è stata derivata costruttivamente.
  - **Termination**: È garantito che ogni funzione del protocollo termini correttamente.

---
*Validazione eseguita automaticamente tramite [GitHub Actions](.github/workflows/agda.no_postulate_well_typed.yml).*














