# ==============================================================================
#      ENGINE PSI-U COMPLETO CON MULTILIBRARY E PRINT INQUADRATO (V3)
# ==============================================================================

PsiU_Complete_MultiLibrary_V3 <- function(raw_input_vector, block_size = 50000, critical_threshold = 71.07) {
  # Tempo di inizio computazione
  tempo_inizio <- Sys.time()
  
  MATTER_THRESHOLD <- 1/3
  SPACE_THRESHOLD  <- 2/3
  G_COSMIC         <- (sqrt(5) - 1) / 3  
  
  N_total  <- length(raw_input_vector)
  n_blocks <- floor(N_total / block_size)
  
  MULTILIBRARY <- list("M1" = numeric(0), "M2" = numeric(0), "M3" = numeric(0))
  
  volumi_box <- 0; volumi_diamond <- 0; volumi_transizione <- 0; volumi_vuoto <- 0
  rami_recisi <- 0
  
  indici_vicinanza_storici <- numeric(n_blocks)
  scostamenti_medi_storici <- numeric(n_blocks)
  valori_risonanza_storici <- numeric(n_blocks)
  
  min_globale <- min(raw_input_vector)
  max_globale <- max(raw_input_vector)
  rng_globale <- max_globale - min_globale
  if (rng_globale == 0) rng_globale <- 1
  
  for (b in 1:n_blocks) {
    idx_start <- ((b - 1) * block_size) + 1
    idx_end   <- b * block_size
    block_grezzo <- raw_input_vector[idx_start:idx_end]
    
    val_p <- (block_grezzo - min_globale) / rng_globale
    
    is_box         <- val_p <= MATTER_THRESHOLD
    is_vuoto       <- val_p > SPACE_THRESHOLD
    in_space       <- !is_box & !is_vuoto
    
    diamond_tolerance <- (SPACE_THRESHOLD - MATTER_THRESHOLD) * 0.5 
    dist_g            <- abs(val_p - G_COSMIC)
    is_diamond        <- in_space & (dist_g <= diamond_tolerance)
    is_transizione    <- in_space & !is_diamond
    
    volumi_box         <- volumi_box + sum(is_box)
    volumi_diamond     <- volumi_diamond + sum(is_diamond)
    volumi_transizione <- volumi_transizione + sum(is_transizione)
    volumi_vuoto       <- volumi_vuoto + sum(is_vuoto)
    
    diamond_grezzo <- block_grezzo[is_diamond]
    
    if (b <= 3) {
      lib_name <- paste0("M", b)
      MULTILIBRARY[[lib_name]] <- block_grezzo[is_box | is_diamond]
      valori_risonanza_storici[b] <- mean(block_grezzo)
      indici_vicinanza_storici[b] <- critical_threshold
      scostamenti_medi_storici[b] <- 0
    } else {
      target_M1 <- mean(MULTILIBRARY$M1)
      target_M2 <- mean(MULTILIBRARY$M2)
      target_M3 <- mean(MULTILIBRARY$M3)
      firma_risonanza_fissa <- mean(c(target_M1, target_M2, target_M3))
      
      if (length(diamond_grezzo) > 0) {
        scostamento_M1 <- mean(abs(diamond_grezzo - target_M1))
        scostamento_M2 <- mean(abs(diamond_grezzo - target_M2))
        scostamento_M3 <- mean(abs(diamond_grezzo - target_M3))
                scostamento_reale_minimo <- min(scostamento_M1, scostamento_M2, scostamento_M3)
        
        # Calcolo scientifico: quanto devia il blocco rispetto alla stabilità del DNA base
        stabilità_base <- sd(c(MULTILIBRARY$M1, MULTILIBRARY$M2, MULTILIBRARY$M3))
        vicinanza_blocco <- (1 - (scostamento_reale_minimo / (stabilità_base * 4))) * 100


        if (vicinanza_blocco < critical_threshold) {
          rami_recisi <- rami_recisi + 1
        }
        indici_vicinanza_storici[b] <- vicinanza_blocco
        scostamenti_medi_storici[b] <- scostamento_reale_minimo
      } else {
        indici_vicinanza_storici[b] <- 0
        scostamenti_medi_storici[b] <- rng_globale
        rami_recisi <- rami_recisi + 1
      }
      # Calcolo scientifico: tolleranza ridotta per massima sensibilità
vicinanza_blocco <- (1 - (scostamento_reale_minimo / (stabilità_base * 1.5))) * 100

    }
  }
  
  tempo_fine <- Sys.time()
  tempo_calcolo <- as.numeric(difftime(tempo_fine, tempo_inizio, units = "secs"))
  
  # Compilazione dell'oggetto strutturato con classe specifica per il print
  report <- list(
    METRICHE_SCALA = c(
      "Volume Totale Flusso (Input)"   = N_total,
      "Dimensione del Vettore Dati"    = object.size(raw_input_vector) / (1024^2), # in MB
      "Rami Recisi per Esclusione"     = rami_recisi
    ),
    VOLUMI_MODALI = data.frame(
      Volume_Assoluto   = c(volumi_box, volumi_diamond, volumi_transizione, volumi_vuoto),
      Quota_Percentuale = c((volumi_box/N_total)*100, (volumi_diamond/N_total)*100, (volumi_transizione/N_total)*100, (volumi_vuoto/N_total)*100),
      row.names         = c("BOX (Materia / Necessita') [ ]", "DIAMOND (Ereditarieta' / Possibilita') [◆]", "TRANSIZIONE OMOTOPICA (Flusso Spaziale)", "VUOTO ESPANSIVO (Mutazione Aperta)")
    ),
    DIAGNOSTICA = c(
      "Firma di Risonanza (Target Fisso)" = tail(valori_risonanza_storici, 1),
      "Scostamento Medio dal DNA Base"    = mean(scostamenti_medi_storici[4:n_blocks], na.rm=TRUE),
      "Indice di Vicinanza Generale"      = mean(indici_vicinanza_storici[4:n_blocks], na.rm=TRUE)
    ),
    BENCHMARK_PRESTAZIONI = c(
      "Tempo di Calcolo CPU Effettivo"   = tempo_calcolo,
      "Velocita' Elaborazione (Through)" = N_total / tempo_calcolo
    )
  )
  
  class(report) <- "PsiU_Inquadrato_Report"
  return(report)
}

# Metodo S3 di Stampa Inquadrato e Allineato
print.PsiU_Inquadrato_Report <- function(x, ...) {
  sep_line <- "========================================================================"
  sub_line <- "------------------------------------------------------------------------"
  
  cat("\n", sep_line, "\n", sep = "")
  cat("           BENCHMARK METRICO INDUSTRIALE - ARCHITETTURA PSI-U           \n")
  cat(sep_line, "\n\n")
  
  cat(" STRUTTURA DELL'ALBERO COMPUTAZIONALE E SCALA\n")
  cat(sub_line, "\n")
  cat(sprintf("  %-40s : %d\n", "Volume Totale Analizzato", x$METRICHE_SCALA[1]))
  cat(sprintf("  %-40s : %.2f MB\n", "Dimensione Vettore in Memoria", x$METRICHE_SCALA[2]))
  cat(sprintf("  %-40s : %d\n", "Rami Recisi per Esclusione (4+)", x$METRICHE_SCALA[3]))
  
  cat("\n MAPPATURA INTEGRALE DEI VOLUMI MODALI\n")
  cat(sub_line, "\n")
  vol_df <- x$VOLUMI_MODALI
  for(i in 1:nrow(vol_df)) {
    cat(sprintf("  %-42s | Vol: %-8d | Quota: %6.3f%%\n", 
                rownames(vol_df)[i], vol_df$Volume_Assoluto[i], vol_df$Quota_Percentuale[i]))
  }
  
  cat("\n DIAGNOSTICA DI RISONANZA E COERENZA OMOTOPIA\n")
  cat(sub_line, "\n")
  cat(sprintf("  %-40s : %.5f\n", "Firma Reale di Risonanza (Target)", x$DIAGNOSTICA[1]))
  cat(sprintf("  %-40s : %.5f\n", "Scostamento Medio dal DNA di Base", x$DIAGNOSTICA[2]))
  cat(sprintf("  %-40s : %.2f%%\n", "Indice di Vicinanza Generale", x$DIAGNOSTICA[3]))
  
  cat("\n METRICHE DI VELOCITA' INDUSTRIALE COMPILATE\n")
  cat(sub_line, "\n")
  cat(sprintf("  %-40s : %.4f secondi\n", "Tempo di Calcolo CPU", x$BENCHMARK_PRESTAZIONI[1]))
  cat(sprintf("  %-40s : %.2f record/secondo\n", "Throughput Operativo", x$BENCHMARK_PRESTAZIONI[2]))
  
  cat(sep_line, "\n")
}
