# ==============================================================================
# ARCHITECTURE: PSI-U ENGINE V3 - MODAL LOGIC & GNOMONIC RESONANCE
# AUTHOR: ROBERTO LOMBARDI
# DATE: 13/06/2026
# LICENSE: CC BY-NC-ND 4.0 (Attribution-NonCommercial-NoDerivs)
# ------------------------------------------------------------------------------
# DESCRIPTION:
# We developed this engine to detect structural resonance within data flows.
# We use a Gnomonic Center of Gravity to filter noise and isolate coherence.
# ==============================================================================

PsiU_Complete_MultiLibrary_V3 <- function(raw_input_vector, block_size = 50000, critical_threshold = 71.07) {
  # We record the start time of the computation
  start_time <- Sys.time()
  
  # Logical constants: We define the modal boundaries
  MATTER_THRESHOLD <- 1/3
  SPACE_THRESHOLD  <- 2/3
  G_COSMIC         <- (sqrt(5) - 1) / 3  # The Gnomonic Constant
  
  N_total  <- length(raw_input_vector)
  n_blocks <- floor(N_total / block_size)
  
  # Memory structures: We initialize the MultiLibrary for DNA imprinting
  MULTILIBRARY <- list("M1" = numeric(0), "M2" = numeric(0), "M3" = numeric(0))
  
  vol_box <- 0; vol_diamond <- 0; vol_trans <- 0; vol_void <- 0
  pruned_branches <- 0
  
  proximity_history <- numeric(n_blocks)
  deviation_history <- numeric(n_blocks)
  resonance_history <- numeric(n_blocks)
  
  # Global range calculation
  min_g <- min(raw_input_vector)
  max_g <- max(raw_input_vector)
  rng_g <- max_g - min_g
  if (rng_g == 0) rng_g <- 1
  
  for (b in 1:n_blocks) {
    idx_start <- ((b - 1) * block_size) + 1
    idx_end   <- b * block_size
    raw_block <- raw_input_vector[idx_start:idx_end]
    
    # Modal Projection: We map data into the modal space
    val_p <- (raw_block - min_g) / rng_g
    is_box   <- val_p <= MATTER_THRESHOLD
    is_void  <- val_p > SPACE_THRESHOLD
    in_space <- !is_box & !is_void
    
    diamond_tol <- (SPACE_THRESHOLD - MATTER_THRESHOLD) * 0.5 
    is_diamond  <- in_space & (abs(val_p - G_COSMIC) <= diamond_tol)
    is_trans    <- in_space & !is_diamond
    
    # We accumulate volumes for modal mapping
    vol_box   <- vol_box + sum(is_box)
    vol_diamond <- vol_diamond + sum(is_diamond)
    vol_trans <- vol_trans + sum(is_trans)
    vol_void  <- vol_void + sum(is_void)
    
    diamond_raw <- raw_block[is_diamond]
    
    if (b <= 3) {
      # Imprinting Phase: We build our reference DNA
      lib_name <- paste0("M", b)
      MULTILIBRARY[[lib_name]] <- raw_block[is_box | is_diamond]
      resonance_history[b] <- mean(raw_block)
      proximity_history[b] <- critical_threshold
    } else {
      # Operational Phase: We analyze resonance stability
      # We calculate the base stability using standard deviation
      base_stability <- sd(c(MULTILIBRARY$M1, MULTILIBRARY$M2, MULTILIBRARY$M3))
      targets <- sapply(MULTILIBRARY, mean)
      fixed_resonance_signature <- mean(targets)
      
      if (length(diamond_raw) > 0) {
        # We calculate the minimum deviation from our Gnomonic targets
        min_real_deviation <- min(abs(mean(diamond_raw) - targets))
        
        # Rigorous Sensitivity Filter: We apply the 1.5x SD constraint
        block_proximity <- (1 - (min_real_deviation / (base_stability * 1.5))) * 100
        
        # Pruning Logic: We discard branches below the critical threshold
        if (block_proximity < critical_threshold) {
            pruned_branches <- pruned_branches + 1
        }
        
        proximity_history[b] <- block_proximity
        deviation_history[b] <- min_real_deviation
      } else {
        # Branch is automatically pruned if no Diamond data is found
        proximity_history[b] <- 0
        deviation_history[b] <- rng_g
        pruned_branches <- pruned_branches + 1
      }
      resonance_history[b] <- fixed_resonance_signature
    }
  }
  
  # Report Compilation: We structure our final findings
  calc_time <- as.numeric(difftime(Sys.time(), start_time, units = "secs"))
  
  report <- list(
    METRICS_SCALE = c(
      "Total Volume Processed" = N_total,
      "Vector Memory Size MB"  = as.numeric(object.size(raw_input_vector) / (1024^2)),
      "Pruned Branches (Anom)" = pruned_branches
    ),
    MODAL_VOLUMES = data.frame(
      Absolute_Volume = c(vol_box, vol_diamond, vol_trans, vol_void),
      Percentage_Share = c(vol_box, vol_diamond, vol_trans, vol_void)/N_total*100,
      row.names = c("BOX (Matter)", "DIAMOND (Resonance)", "TRANSITION", "VOID (Mutation)")
    ),
    DIAGNOSTICS = c(
      "Target Resonance Signature" = tail(resonance_history, 1),
      "Average Deviation"          = mean(deviation_history[4:n_blocks], na.rm=TRUE),
      "General Proximity Index %"  = mean(proximity_history[4:n_blocks], na.rm=TRUE)
    ),
    PERFORMANCE = c(
      "CPU Calculation Time"       = calc_time,
      "Throughput (rec/sec)"       = N_total / calc_time
    )
  )
  
  class(report) <- "PsiU_Industrial_Report"
  return(report)
}

# S3 Print Method: We present the data in an industrial format
print.PsiU_Industrial_Report <- function(x, ...) {
  sep <- "========================================================================"
  cat("\n", sep, "\n           INDUSTRIAL METRIC BENCHMARK - PSI-U ARCHITECTURE           \n", sep, "\n\n")
  
  cat(" COMPUTATIONAL TREE STRUCTURE AND SCALE\n------------------------------------------------------------------------\n")
  for(i in 1:3) cat(sprintf("  %-40s : %s\n", names(x$METRICS_SCALE)[i], format(x$METRICS_SCALE[i], scientific=F)))
  
  cat("\n INTEGRAL MODAL VOLUME MAPPING\n------------------------------------------------------------------------\n")
  df <- x$MODAL_VOLUMES
  for(i in 1:4) cat(sprintf("  %-42s | Vol: %-8d | Share: %6.3f%%\n", rownames(df)[i], df[i,1], df[i,2]))
  
  cat("\n RESONANCE DIAGNOSTICS\n------------------------------------------------------------------------\n")
  for(i in 1:3) cat(sprintf("  %-40s : %.5f\n", names(x$DIAGNOSTICS)[i], x$DIAGNOSTICS[i]))
  
  cat("\n PERFORMANCE METRICS\n------------------------------------------------------------------------\n")
  cat(sprintf("  %-40s : %.4f sec\n  %-40s : %.2f\n", names(x$PERFORMANCE)[1], x$PERFORMANCE[1], names(x$PERFORMANCE)[2], x$PERFORMANCE[2]))
  
  cat("\n AUTHOR: ROBERTO LOMBARDI - 13/06/2026 - COPYRIGHT RESERVED\n")
  cat(sep, "\n")
}
