# =========================================================================
# AUDIT FINALE: STRESS TEST SUI PUNTI DI TRANSIZIONE CRITICI
# =========================================================================

library(PsiUEngineRL)

G_TARGET <- 0.6180339887

# GENERAZIONE DI COPPIE AL LIMITE ESTREMO DEL CONFINE (MICRO-VARIAZIONI)
# Soglia BOX = 0.002 | Soglia DIAMOND = 0.010
valore_box_limite     <- G_TARGET + 0.00199999  # Deve essere BOX
valore_diamond_inizio <- G_TARGET + 0.00200001  # Deve essere DIAMOND

valore_diamond_limite <- G_TARGET + 0.00999999  # Deve essere DIAMOND
valore_noise_inizio   <- G_TARGET + 0.01000001  # Deve essere NOISE

flusso_stress <- c(valore_box_limite, valore_diamond_inizio, valore_diamond_limite, valore_noise_inizio)

# ELABORAZIONE TRAMITE IL MOTORE UFFICIALE
message("[INFO] Analisi microscopica sui confini di transizione modale...")
res_stress <- PsiU_Engine_RL(flusso_stress)

# VERIFICA PUNTUALE DEGLI STATI ASSEGNATI
is_box_ok   <- grepl("BOX", res_stress$Stato_Modale[1])
is_dia1_ok  <- grepl("DIAMOND", res_stress$Stato_Modale[2])
is_dia2_ok  <- grepl("DIAMOND", res_stress$Stato_Modale[3])
is_noise_ok <- grepl("NOISE", res_stress$Stato_Modale[4])

cat("\n=======================================================\n")
cat(" RISULTATI DELLO STRESS TEST SUI CONFINI DELLA RATIO \n")
cat("=======================================================\n")
cat("Confine BOX/DIAMOND (Sotto il limite): ", res_stress$Stato_Modale[1], " -> ", ifelse(is_box_ok, "OK", "FALLITO"), "\n")
cat("Confine BOX/DIAMOND (Sopra il limite): ", res_stress$Stato_Modale[2], " -> ", ifelse(is_dia1_ok, "OK", "FALLITO"), "\n")
cat("Confine DIAMOND/NOISE (Sotto il limite): ", res_stress$Stato_Modale[3], " -> ", ifelse(is_dia2_ok, "OK", "FALLITO"), "\n")
cat("Confine DIAMOND/NOISE (Sopra il limite): ", res_stress$Stato_Modale[4], " -> ", ifelse(is_noise_ok, "OK", "FALLITO"), "\n")
cat("-------------------------------------------------------\n")

# CRITERIO RIGIDO DI ACCETTAZIONE AL MILLESIMO
if (is_box_ok && is_dia1_ok && is_dia2_ok && is_noise_ok) {
  cat("[SUCCESSO] La risoluzione numerica della Gnomonic Ratio è perfetta al microscopio.\n")
} else {
  stop("[FALLIMENTO] Il motore ha mostrato incertezza o arrotondamenti errati sui punti di transizione.")
}
cat("=======================================================\n")
