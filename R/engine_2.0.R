PsiU_Complete_MultiLibrary_V3 <- function(raw_input_vector, block_size = 50000, critical_threshold = 71.07) {
  tempo_inizio <- Sys.time()
  
  # Costanti Logiche
  MATTER_THRESHOLD <- 1/3
  SPACE_THRESHOLD  <- 2/3
  G_COSMIC         <- (sqrt(5) - 1) / 3  
  
  N_total  <- length(raw_input_vector)
  n_blocks <- floor(N_total / block_size)
  
  # Strutture di Memoria
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
    
    # Proiezione Modale
    val_p <- (block_grezzo - min_globale) / rng_globale
    is_box <- val_p <= MATTER_THRESHOLD
    is_vuoto <- val_p > SPACE_THRESHOLD
    in_space <- !is_box & !is_vuoto
    
    diamond_tolerance <- (SPACE_THRESHOLD - MATTER_THRESHOLD) * 0.5 
    is_diamond <- in_space & (abs(val_p - G_COSMIC) <= diamond_tolerance)
    is_transizione <- in_space & !is_diamond
    
    # Accumulo Volumi
    volumi_box <- volumi_box + sum(is_box)
    volumi_diamond <- volumi_diamond + sum(is_diamond)
    volumi_transizione <- volumi_transizione + sum(is_transizione)
    volumi_vuoto <- volumi_vuoto + sum(is_vuoto)
    
    diamond_grezzo <- block_grezzo[is_diamond]
    
    if (b <= 3) {
      # Fase di Imprinting DNA
      lib_name <- paste0("M", b)
      MULTILIBRARY[[lib_name]] <- block_grezzo[is_box | is_diamond]
      valori_risonanza_storici[b] <- mean(block_grezzo)
      indici_vicinanza_storici[b] <- critical_threshold
    } else {
      # Fase Operativa: Analisi di Risonanza
      stabilità_base <- sd(c(MULTILIBRARY$M1, MULTILIBRARY$M2, MULTILIBRARY$M3))
      targets <- sapply(MULTILIBRARY, mean)
      firma_risonanza_fissa <- mean(targets)
      
      if (length(diamond_grezzo) > 0) {
        # Calcolo scostamento dal baricentro gnomonico
        scostamento_reale_minimo <- min(abs(mean(diamond_grezzo) - targets))
        
        # FILTRO DI SENSIBILITA' (1.5x SD per rigore scientifico)
        vicinanza_blocco <- (1 - (scostamento_reale_minimo / (stabilità_base * 1.5))) * 100
        
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
      valori_risonanza_storici[b] <- firma_risonanza_fissa
    }
  }
  
  # Compilazione Report
  tempo_calcolo <- as.numeric(difftime(Sys.time(), tempo_inizio, units = "secs"))
  report <- list(
    METRICHE_SCALA = c(
      "Volume Totale Flusso"   = N_total,
      "Dimensione Vettore MB"  = as.numeric(object.size(raw_input_vector) / (1024^2)),
      "Rami Recisi (Anomalie)" = rami_recisi
    ),
    VOLUMI_MODALI = data.frame(
      Volume_Assoluto = c(volumi_box, volumi_diamond, volumi_transizione, volumi_vuoto),
      Quota_Percentuale = c(volumi_box, volumi_diamond, volumi_transizione, volumi_vuoto)/N_total*100,
      row.names = c("BOX (Materia) [ ]", "DIAMOND (Ereditarieta') [◆]", "TRANSIZIONE OMOTOPICA", "VUOTO ESPANSIVO")
    ),
    DIAGNOSTICA = c(
      "Firma Risonanza Target" = tail(valori_risonanza_storici, 1),
      "Scostamento Medio"      = mean(scostamenti_medi_storici[4:n_blocks], na.rm=TRUE),
      "Vicinanza Generale %"   = mean(indici_vicinanza_storici[4:n_blocks], na.rm=TRUE)
    ),
    BENCHMARK_PRESTAZIONI = c(
      "Tempo Calcolo CPU"      = tempo_calcolo,
      "Throughput (rec/sec)"   = N_total / tempo_calcolo
    )
  )
  class(report) <- "PsiU_Inquadrato_Report"
  return(report)
}

# Metodo di Stampa
print.PsiU_Inquadrato_Report <- function(x, ...) {
  sep <- "========================================================================"
  cat("\n", sep, "\n           BENCHMARK METRICO INDUSTRIALE - ARCHITETTURA PSI-U           \n", sep, "\n\n")
  cat(" STRUTTURA DELL'ALBERO E SCALA\n------------------------------------------------------------------------\n")
  for(i in 1:3) cat(sprintf("  %-40s : %s\n", names(x$METRICHE_SCALA)[i], format(x$METRICHE_SCALA[i], scientific=F)))
  cat("\n MAPPATURA VOLUMI MODALI\n------------------------------------------------------------------------\n")
  df <- x$VOLUMI_MODALI
  for(i in 1:4) cat(sprintf("  %-42s | Vol: %-8d | Quota: %6.3f%%\n", rownames(df)[i], df[i,1], df[i,2]))
  cat("\n DIAGNOSTICA DI RISONANZA\n------------------------------------------------------------------------\n")
  for(i in 1:3) cat(sprintf("  %-40s : %.5f\n", names(x$DIAGNOSTICA)[i], x$DIAGNOSTICA[i]))
  cat("\n PERFORMANCE\n------------------------------------------------------------------------\n")
  cat(sprintf("  %-40s : %.4f sec\n  %-40s : %.2f\n", names(x$BENCHMARK_PRESTAZIONI)[1], x$BENCHMARK_PRESTAZIONI[1], names(x$BENCHMARK_PRESTAZIONI)[2], x$BENCHMARK_PRESTAZIONI[2]))
  cat(sep, "\n")
}
