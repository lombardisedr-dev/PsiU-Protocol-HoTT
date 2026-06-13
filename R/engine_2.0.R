# ==============================================================================
#                      ARCHITETTURA UNIFICATA PSI-U ENGINE
#                     CONSOLIDAMENTO METRICO E LOGICA MODALE
# ==============================================================================

#' @title Motore MultiLibrary Analitico e Benchmark Metrico
#' @description Valuta flussi di dati su macro-volumi applicando la ripartizione 
#' geometrica di 1/3 (Materia) e 2/3 (Spazio) con risonanza gnomonica proiettiva.
#' @param raw_input_vector Vettore numerico grezzo contenente il flusso di dati.
#' @return Un oggetto di classe 'PsiU_Report' contenente scala, volumi e diagnostica.
#' @export
PsiU_MultiLibrary_Benchmark <- function(raw_input_vector) {
  
  # 1. PARAMETRI E COSTANTI GEOMETRICHE DELLA TEORIA
  MATTER_THRESHOLD <- 1/3   # 0.33333... (Il primo terzo per la materia)
  SPACE_THRESHOLD  <- 2/3   # 0.66667... (I due terzi complessivi di spazio)
  
  # La Sezione Aurea proiettata nello spazio ereditario
  G_COSMIC <- SPACE_THRESHOLD * 0.6180339887 # ~0.41202
  
  # Tolleranza omotopica per agganciare il canale ereditario DIAMOND
  DIAMOND_TOLERANCE <- (SPACE_THRESHOLD - MATTER_THRESHOLD) * 0.5 

  # 2. LIMITI DI SCALA REALI E ACQUISIZIONE INPUT
  min_val <- min(raw_input_vector)
  max_val <- max(raw_input_vector)
  rng <- max_val - min_val
  if (rng == 0) rng <- 1
  
  # 3. NORMALIZZAZIONE PROIETTIVA (Scala Unificata 0-1)
  val_p <- (raw_input_vector - min_val) / rng

  # 4. OPERAZIONI LOGICHE VETTORIALIZZATE (Smistamento ad Alta Performance)
  is_box   <- val_p <= MATTER_THRESHOLD
  is_vuoto <- val_p > SPACE_THRESHOLD
  in_space <- !is_box & !is_vuoto
  
  dist_g         <- abs(val_p - G_COSMIC)
  is_diamond     <- in_space & (dist_g <= DIAMOND_TOLERANCE)
  is_transizione <- in_space & !is_diamond

  # Estrazione dei segmenti di flusso grezzi e proiettati
  box_crystal_grezzo     <- raw_input_vector[is_box]
  box_crystal_p          <- val_p[is_box]
  diamond_reserve_grezzo <- raw_input_vector[is_diamond]
  diamond_reserve_p      <- val_p[is_diamond]
  transizione_p          <- val_p[is_transizione]
  vuoto_p                <- val_p[is_vuoto]

  # 5. COMPILATORE ANALITICO DELLA RISONANZA DEL PRESENTE
  if (length(box_crystal_p) > 0) {
    target_proiettato         <- mean(box_crystal_p)
    VALORE_REALE_DI_RISONANZA <- mean(box_crystal_grezzo)
    
    # Calcolo degli scostamenti basati sulla scala reale dei dati
    scostamenti_grezzi        <- abs(diamond_reserve_grezzo - VALORE_REALE_DI_RISONANZA)
    scostamento_medio_reale   <- mean(scostamenti_grezzi)
    scostamento_minimo_reale  <- min(scostamenti_grezzi)
    scostamento_massimo_reale <- max(scostamenti_grezzi)
    
    # Indice di vicinanza percentuale basato sulla deviazione proiettata
    scostamento_medio_p          <- mean(abs(diamond_reserve_p - target_proiettato))
    indice_vicinanza_percentuale <- (1 - scostamento_medio_p) * 100
  } else {
    VALORE_REALE_DI_RISONANZA <- NA
    scostamento_medio_reale   <- NA
    scostamento_minimo_reale  <- NA
    scostamento_massimo_reale <- NA
    indice_vicinanza_percentuale <- 0
  }

  # 6. STRUTTURAZIONE DEL REPORT STRUTTURATO
  report <- list(
    SCALA_INPUT = c(
      "Valore Minimo Assoluto"     = min_val,
      "Valore Massimo Assoluto"    = max_val,
      "Estensione del Range (Rng)" = rng
    ),
    VOLUMI_MODALI = data.frame(
      Volume_Assoluto   = c(length(raw_input_vector), length(box_crystal_p), length(diamond_reserve_p), length(transizione_p), length(vuoto_p)),
      Quota_Percentuale = c(100.0, (length(box_crystal_p)/length(val_p))*100, (length(diamond_reserve_p)/length(val_p))*100, (length(transizione_p)/length(val_p))*100, (length(vuoto_p)/length(val_p))*100),
      row.names         = c("Volume Totale Flusso", "BOX (Materia / Necessità) [\u25a1]", "DIAMOND (Ereditarietà / Possibilità) [\u25c6]", "TRANSIZIONE OMOTOPICA (Flusso Spaziale)", "VUOTO ESPANSIVO (Mutazione Aperta)")
    ),
    DIAGNOSTICA_RISONANZA = c(
      "IL SISTEMA STA RISUONANDO AL VALORE REALE" = VALORE_REALE_DI_RISONANZA,
      "Scostamento Medio dai dati presenti"       = scostamento_medio_reale,
      "Scostamento Minimo (Massima Sintonia)"     = scostamento_minimo_reale,
      "Scostamento Massimo (Massima Distanza)"    = scostamento_massimo_reale,
      "Indice di Vicinanza Generale al Presente"  = indice_vicinanza_percentuale
    )
  )
  
  class(report) <- "PsiU_Report"
  return(report)
}

#' @title Funzione di Stampa S3 per PsiU_Report
#' @description Garantisce l'ordinamento sequenziale rigido e la formattazione pulita dell'output.
#' @export
print.PsiU_Report <- function(x, ...) {
  cat("\n========================================================================\n")
  cat("                BENCHMARK METRICO - PSIU MULTILIBRARY                 \n")
  cat("========================================================================\n\n")
  
  cat(" DATI DI SCALA REALI (INPUT)\n")
  cat("------------------------------------------------------------------------\n")
  for (i in seq_along(x$SCALA_INPUT)) {
    cat(sprintf("  %-35s : %.5f\n", names(x$SCALA_INPUT)[i], x$SCALA_INPUT[i]))
  }
  
  cat("\n MAPPATURA DEI VOLUMI MODALI\n")
  cat("------------------------------------------------------------------------\n")
  print(round(x$VOLUMI_MODALI, 5))
  
  cat("\n DIAGNOSTICA DI RISONANZA DEL PRESENTE\n")
  cat("------------------------------------------------------------------------\n")
  cat(sprintf("  -> %-40s : %.5f\n", names(x$DIAGNOSTICA_RISONANZA)[1], x$DIAGNOSTICA_RISONANZA[1]))
  cat(sprintf("  %-43s : %.5f\n", names(x$DIAGNOSTICA_RISONANZA)[2], x$DIAGNOSTICA_RISONANZA[2]))
  cat(sprintf("  %-43s : %.5f\n", names(x$DIAGNOSTICA_RISONANZA)[3], x$DIAGNOSTICA_RISONANZA[3]))
  cat(sprintf("  %-43s : %.5f\n", names(x$DIAGNOSTICA_RISONANZA)[4], x$DIAGNOSTICA_RISONANZA[4]))
  cat(sprintf("  %-43s : %.2f%%\n", names(x$DIAGNOSTICA_RISONANZA)[5], x$DIAGNOSTICA_RISONANZA[5]))
  cat("========================================================================\n")
}
