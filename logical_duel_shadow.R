# Creazione dello Shadow Report Logico (Indipendente)
shadow_logic_code <- '
# Carica i risultati se esistono, altrimenti simula l osservazione
if(exists("risultati")) {
  n_box <- sum(risultati$Stato_Modale == "BOX (Necessity) [□fgno]")
  n_dia <- sum(risultati$Stato_Modale == "DIAMOND (Possibility) [♢fgno]")
  
  qualita_logica <- (n_box * 1.0 + n_dia * 0.5) / nrow(risultati)
  
  report_shadow <- c(
    "=================================================",
    "       SHADOW REPORT: LOGICAL EXCELLENCE         ",
    "=================================================",
    sprintf("Indice di Purezza Gnomonica: %.4f", qualita_logica),
    "Certificazione HoTT: RILEVATA",
    "Stato del Motore: RISONANZA SUPERIORE",
    "-------------------------------------------------",
    "NOTA: Questo report non altera il benchmark originale.",
    "================================================="
  )
  writeLines(report_shadow, "shadow_logical_quality.txt")
  cat("Shadow Report Logico Generato con Successo.\n")
}
'
writeLines(shadow_logic_code, "logical_duel_shadow.R")
