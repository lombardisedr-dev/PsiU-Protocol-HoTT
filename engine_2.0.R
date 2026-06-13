PsiU_Complete_MultiLibrary_V3 <- function(raw_input_vector, block_size = 50000, critical_threshold = 71.07) {
  start_time <- Sys.time()
  
  # Costanti Logiche e Gnomoniche
  MATTER_THRESHOLD <- 1/3
  SPACE_THRESHOLD  <- 2/3
  G_COSMIC         <- (sqrt(5) - 1) / 3 
  
  N_total  <- length(raw_input_vector)
  n_blocks <- floor(N_total / block_size)
  
  # Strutture di Memoria
  MULTILIBRARY <- list("M1" = numeric(0), "M2" = numeric(0), "M3" = numeric(0))
  vol_box <- 0; vol_diamond <- 0; vol_trans <- 0; vol_void <- 0
  pruned_branches <- 0
  
  proximity_history <- numeric(n_blocks)
  deviation_history <- numeric(n_blocks)
  resonance_history <- numeric(n_blocks)
  
  # Calcolo Range Globale (Anti-NA)
  min_g <- min(raw_input_vector, na.rm = TRUE)
  max_g <- max(raw_input_vector, na.rm = TRUE)
  rng_g <- max_g - min_g
  if (is.na(rng_g) || rng_g == 0) rng_g <- 1

  # --- INIZIO CICLO DI ANALISI ---
  for (b in 1:n_blocks) {
    idx_start <- ((b - 1) * block_size) + 1
    idx_end   <- b * block_size
    raw_block <- raw_input_vector[idx_start:idx_end]
    
    # Proiezione Modale
    val_p <- (raw_block - min_g) / rng_g
    is_box   <- val_p <= MATTER_THRESHOLD
    is_void  <- val_p > SPACE_THRESHOLD
    in_space <- !is_box & !is_void
    
    diamond_tol <- (SPACE_THRESHOLD - MATTER_THRESHOLD) * 0.5 
    is_diamond  <- in_space & (abs(val_p - G_COSMIC) <= diamond_tol)
    is_trans    <- in_space & !is_diamond
    
    # Accumulo Volumi
    vol_box     <- vol_box + sum(is_box)
    vol_diamond <- vol_diamond + sum(is_diamond)
    vol_trans   <- vol_trans + sum(is_trans)
    vol_void    <- vol_void + sum(is_void)
    
    diamond_raw <- raw_block[is_diamond]
    
    if (b <= 3) {
      # Fase di Imprinting DNA
      lib_name <- paste0("M", b)
      MULTILIBRARY[[lib_name]] <- raw_block[is_box | is_diamond]
      resonance_history[b] <- mean(raw_block, na.rm=TRUE)
      proximity_history[b] <- critical_threshold
    } else {
      # Fase Operativa: Analisi Resonanza
      base_stability <- sd(c(MULTILIBRARY$M1, MULTILIBRARY$M2, MULTILIBRARY$M3), na.rm=TRUE)
      targets <- sapply(MULTILIBRARY, mean, na.rm=TRUE)
      
      if (length(diamond_raw) > 0) {
        min_real_deviation <- min(abs(mean(diamond_raw) - targets))
        block_proximity <- (1 - (min_real_deviation / (base_stability * 1.5))) * 100
        
        if (block_proximity < critical_threshold) pruned_branches <- pruned_branches + 1
        
        proximity_history[b] <- block_proximity
        deviation_history[b] <- min_real_deviation
      } else {
        proximity_history[b] <- 0
        pruned_branches <- pruned_branches + 1
      }
      resonance_history[b] <- mean(targets)
    }
  }
  
  # Compilazione Report Finale
  calc_time <- as.numeric(difftime(Sys.time(), start_time, units = "secs"))
  report <- list(
    METRICS_SCALE = c("Total Volume" = N_total, "Pruned Branches" = pruned_branches),
    MODAL_VOLUMES = data.frame(
      Absolute_Volume = c(vol_box, vol_diamond, vol_trans, vol_void),
      Percentage_Share = c(vol_box, vol_diamond, vol_trans, vol_void)/N_total*100,
      row.names = c("BOX", "DIAMOND", "TRANSITION", "VOID")),
    DIAGNOSTICS = c("Target Resonance" = tail(resonance_history, 1), 
                    "Gen. Proximity %" = mean(proximity_history[4:n_blocks], na.rm=TRUE)),
    PERFORMANCE = c("Throughput" = N_total / calc_time)
  )
  class(report) <- "PsiU_Industrial_Report"
  return(report)
}
