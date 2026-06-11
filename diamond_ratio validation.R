# =========================================================================
# AUDIT MIRATO: VALIDAZIONE FORMALE SULLO STATO MODALE DIAMOND
# =========================================================================

library(PsiUEngineRL)

# Costante invariante ufficiale estratta dal codice sorgente
G_TARGET <- 0.6180339887
n_punti  <- 100

# GENERAZIONE FLUSSO CALIBRATO SULLA SOGLIA INTERMEDIA DIAMOND
# La regola J assegna DIAMOND se la distanza è compresa tra 0.002 e 0.010
# Generiamo punti che distano esattamente circa 0.005 da G
flusso_diamond <- runif(n_punti, min = G_TARGET + 0.004, max = G_TARGET + 0.006)

# ELABORAZIONE TRAMITE IL MOTORE UFFICIALE
message("[INFO] Analisi del flusso a soglia intermedia (DIAMOND)...")
res_diamond <- PsiU_Engine_RL(flusso_diamond)

# ESTRAZIONE E CONTEGGIO
punti_dia_in_dia <- sum(grepl("DIAMOND", res_diamond$Stato_Modale), na.rm = TRUE)
acc_dia          <- (punti_dia_in_dia / n_punti) * 100

cat("\n=======================================================\n")
cat(" RISULTATI DELL'AUDIT MIRATO: DOMINIO DIAMOND \n")
cat("=======================================================\n")
cat("Nodi identificati come DIAMOND (Possibilità): ", punti_dia_in_dia, "/", n_punti, " (", acc_dia, "%)\n", sep="")
cat("-------------------------------------------------------\n")

# CRITERI DI ACCETTAZIONE SCIENTIFICA
if (acc_dia == 100) {
  cat("[SUCCESSO] La finestra modale DIAMOND risponde perfettamente alle specifiche geometriche.\n")
} else {
  stop("[FALLIMENTO] Il motore non ha intercettato correttamente la zona di possibilità.")
}
cat("=======================================================\n")
