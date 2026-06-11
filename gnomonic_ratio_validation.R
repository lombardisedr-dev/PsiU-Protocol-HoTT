# =========================================================================
# AUDIT COMPUTAZIONALE V3: VALIDAZIONE SELETTIVITÀ DELLA GNOMONIC RATIO
# =========================================================================

library(PsiUEngineRL)

# 1. Riproducibilità geometrica
set.seed(2026)
n_punti <- 200

# 2. Generazione dei flussi d'identità omotopici
flusso_box   <- sin(seq(0, 4 * pi, length.out = n_punti)) # Ordinato (Necessità)
flusso_noise <- rnorm(n_punti, mean = 0, sd = 3.0)        # Caotico (Rumore)

# 3. Processamento tramite il motore HoTT
message("[INFO] Analisi del flusso deterministico (BOX)...")
res_box   <- PsiU_Engine_RL(flusso_box)

message("[INFO] Analisi del flusso caotico (NOISE)...")
res_noise <- PsiU_Engine_RL(flusso_noise)

# 4. Estrazione sicura della classificazione dei nodi del Tableau Tree
punti_box_in_box <- sum(res_box$categories == "BOX", na.rm = TRUE)
punti_noise_in_noise <- sum(res_noise$categories == "NOISE", na.rm = TRUE)

# Calcolo dell'accuratezza (Selettività Topologica)
accuratezza_segnale <- (punti_box_in_box / n_punti) * 100
accuratezza_rumore  <- (punti_noise_in_noise / n_punti) * 100

cat("\n===============================================\n")
cat(" RISULTATI DELL'AUDIT DELLA GNOMONIC RATIO \n")
cat("===============================================\n")
cat("Nodi Riconosciuti come BOX nel Segnale:   ", punti_box_in_box, "/", n_punti, " (", accuratezza_segnale, "%)\n", sep="")
cat("Nodi Riconosciuti come NOISE nel Caos:    ", punti_noise_in_noise, "/", n_punti, " (", accuratezza_rumore, "%)\n", sep="")
cat("-----------------------------------------------\n")

# 5. Criterio Rigido di Onestà Algoritmica
if (is.na(accuratezza_segnale) || is.na(accuratezza_rumore)) {
  stop("[ERRORE] Le metriche estratte contengono valori non validi (NA).")
}

if (accuratezza_segnale < 50 || accuratezza_rumore < 50) {
  stop("[FALLIMENTO] La Gnomonic Ratio non ha raggiunto la selettività topologica minima del 50%.")
} else {
  cat("[SUCCESSO] Onestà algoritmica validata con successo.\n")
}
cat("===============================================\n")
