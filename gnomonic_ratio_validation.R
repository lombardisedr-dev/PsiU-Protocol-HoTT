# =========================================================================
# AUDIT COMPUTAZIONALE: VALIDAZIONE DELLA GNOMONIC RATIO [Lombardi, 2026]
# =========================================================================

# Forza il caricamento del pacchetto installato nella libreria utente
.libPaths(c(Sys.getenv("R_LIBS_USER"), .libPaths()))
library(PsiUEngineRL)

# 1. Riproducibilità del Protocollo Geometrico
set.seed(2026)
n_punti <- 200

# 2. Generazione dei flussi d'identità omotopici
# Controllo Positivo (Necessità - Geodetica strutturata)
flusso_box   <- sin(seq(0, 4 * pi, length.out = n_punti))

# Controllo Negativo (Caos - Entropia pura senza struttura)
flusso_noise <- rnorm(n_punti, mean = 0, sd = 3.0)

# 3. Processamento tramite il motore HoTT
message("[INFO] Analisi del flusso deterministico (BOX)...")
res_box   <- PsiU_Engine_RL(flusso_box)

message("[INFO] Analisi del flusso caotico (NOISE)...")
res_noise <- PsiU_Engine_RL(flusso_noise)

# 4. Estrazione delle metriche di Entropia Strutturale
entropy_box   <- mean(res_box$structural_entropy)
entropy_noise <- mean(res_noise$structural_entropy)

cat("\n===============================================\n")
cat(" RISULTATI DELL'AUDIT DELLA GNOMONIC RATIO \n")
cat("===============================================\n")
cat("Entropia Strutturale (Segnale Ordinato): ", entropy_box, "\n")
cat("Entropia Strutturale (Rumore Caotico):    ", entropy_noise, "\n")
cat("-----------------------------------------------\n")

# 5. Verifica matematica dei Criteri di Rigetto
# L'invariante deve isolare l'entropia: l'ordine deve avere meno entropia del caos
if (entropy_box >= entropy_noise) {
  stop("[FALLIMENTO] La Gnomonic Ratio non ha isolato correttamente l'entropia strutturale.")
} else {
  cat("[SUCCESSO] Onestà algoritmica validata. La Gnomonic Ratio distingue il caos dall'ordine.\n")
}
cat("===============================================\n")
