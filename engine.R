# PROGETTO: PSIU-PROTOCOL (HoTT-Inspired Data Analysis)
# MOTORE  : GNOMONIC RESONANCE SIEVE v2.0 - "STRESS TEST EDITION"
# AUTORE  : Roberto Lombardi 
# LICENZA : [MIT]

target_gnomonic <- 1/3

# --- 1. CARICAMENTO DATI REALI (Biotest / Smart City) ---
# Smettiamo di generare rumore e leggiamo il file caricato dall'utente
S <- read.csv("input_potential.csv")

# --- 2. ANALISI DI RISONANZA ---
S$scostamento <- abs(S$ratio - target_gnomonic)
S$resonance <- exp(-S$scostamento / sd(S$ratio))

# --- 3. CLASSIFICAZIONE MULTILIBRARY ---
S$library_status <- cut(S$scostamento, 
                       breaks = c(-Inf, 0.01, 0.10, Inf), 
                       labels = c("Library_1 (Necessita)", 
                                  "Library_0 (Possibilita)", 
                                  "Library_-1 (Rumore)"))

S$intensita_risonanza <- round(exp(-S$scostamento * 10), 4)

# --- 4. ESTRAZIONE NUCLEO (Solo Library 1) ---
nucleo <- S[S$library_status == "Library_1 (Necessita)", ]

# --- 5. TEST STATISTICO (Il Giudice) ---
test_box <- t.test(S$ratio, mu = target_gnomonic)

# --- 6. OUTPUT FINALE (I Documenti per Zenodo) ---
write.csv(S, "results_full_analysis.csv", row.names=F)
write.csv(nucleo, "results_core_identified.csv", row.names=F)

report_finale <- data.frame(
  Parametro = c("Campioni_Totali", "Nucleo_Identificato", "P_Value", "Verdetto_Sistemico"),
  Valore = c(
    nrow(S), 
    nrow(nucleo), 
    round(test_box$p.value, 5),
    if(test_box$p.value > 0.05) "CONVERGENT (Necessity)" else "NON_CONVERGENT (Accidental)"
  )
)
write.csv(report_finale, "results_summary_report.csv", row.names=F)
