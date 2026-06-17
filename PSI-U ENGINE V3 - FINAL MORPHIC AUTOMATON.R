# ==============================================================================
# ARCHITECTURE: PSI-U ENGINE V3 - FINAL MORPHIC AUTOMATON
# AUTHOR: ROBERTO LOMBARDI
# DATE: 17/06/2026
# LICENSE: CC BY-NC-ND 4.0 (Attribution-NonCommercial-NoDerivs)
# ------------------------------------------------------------------------------
# DESCRIPTION:
# We developed this final morphic architecture to map dynamic data streams.
# We eliminate static boundaries to let Space and Matter interact freely.
# ==============================================================================

PsiU_Final_Morphic_Engine <- function(raw_input_vector, block_size = 50000, critical_threshold = 71.07) {
  # We record the start time of our morphic computation
  start_time <- Sys.time()
  
  # Immutable Cosmic Gnomonic Constant: We establish our homotopic reference
  G_COSMIC <- (sqrt(5) - 1) / 3 
  
  N_total <- length(raw_input_vector)
  n_blocks <- floor(N_total / block_size)
  
  # Memory structures: We initialize our MultiLibrary for DNA imprinting
  MULTILIBRARY <- list("M1" = numeric(0), "M2" = numeric(0), "M3" = numeric(0))
  
  vol_box <- 0; vol_diamond <- 0; vol_trans <- 0; vol_void <- 0
  pruned_branches <- 0
  proximity_history <- numeric(n_blocks)
  deviation_history <- numeric(n_blocks)
  resonance_history <- numeric(n_blocks)

  for (b in 1:n_blocks) {
    idx_start <- ((b - 1) * block_size) + 1
    idx_end <- b * block_size
    raw_block <- raw_input_vector[idx_start:idx_end]

    # 1. MORPHIC NORMALIZATION (Z-SCORE)
    # We respect the intrinsic density: We do not squash peaks or linearize.
    # We measure how many standard deviations each point lies from the block mean.
    sd_block <- sd(raw_block, na.rm = TRUE)
    if(is.na(sd_block) || sd_block == 0) sd_block <- 1
    mean_block <- mean(raw_block, na.rm = TRUE)
    
    # Normalized geometric mapping: We scale the vector to a standard [-3, +3] range
    val_z <- (raw_block - mean_block) / sd_block
    
    # Absolute amplitude transformation: We set 0 as Mean and 1 as Maximum expected oscillation
    val_p <- abs(val_z) / 3
    val_p[val_p > 1] <- 1 # Safety clip: We handle extreme structural shocks

    # 2. PHILOSOPHICAL SPACE/MATTER SEPARATION (ENERGY-BASED BOUNDARIES)
    # MATTER (Box) resides in our dense, low-energy core close to the mean.
    # EMPTY SPACE (Void) extends into the rarefied outer amplitudes.
    MATTER_THRESHOLD <- 0.33333
    SPACE_THRESHOLD  <- 0.66667
    
    is_box <- val_p <= MATTER_THRESHOLD
    is_void <- val_p > SPACE_THRESHOLD
    in_space <- !is_box & !is_void

    # DIAMOND (Gnomonic Resonance) fluctuates dynamically around the cosmic constant, 
    # calibrated by our Median Absolute Deviation (MAD) of real amplitudes.
    mad_p <- mad(val_p, na.rm = TRUE)
    if(mad_p == 0) mad_p <- 0.1
    diamond_tol <- mad_p * 0.5
    
    is_diamond <- in_space & (abs(val_p - G_COSMIC) <= diamond_tol)
    is_trans <- in_space & !is_diamond

    # Volume Accumulation: We record our real dynamic volumes
    vol_box <- vol_box + sum(is_box)
    vol_diamond <- vol_diamond + sum(is_diamond)
    vol_trans <- vol_trans + sum(is_trans)
    vol_void <- vol_void + sum(is_void)

    diamond_raw <- raw_block[is_diamond]

    # 3. IMPRINTING PHASE AND RESONANCE ANALYSIS
    if (b <= 3) {
      # We build our reference DNA profile during the first three blocks
      lib_name <- paste0("M", b)
      MULTILIBRARY[[lib_name]] <- raw_block[is_box | is_diamond]
      resonance_history[b] <- mean(raw_block)
      proximity_history[b] <- critical_threshold
    } else {
      # Operational Phase: We evaluate structural stability against our DNA targets
      base_stability <- sd(c(MULTILIBRARY$M1, MULTILIBRARY$M2, MULTILIBRARY$M3), na.rm=TRUE)
      targets <- sapply(MULTILIBRARY, mean)
      fixed_resonance_signature <- mean(targets)

      if (length(diamond_raw) > 0 && !is.na(base_stability) && base_stability > 0) {
        # We calculate the exact topological gap from our gnomonic targets
        min_real_deviation <- min(abs(mean(diamond_raw) - targets))
        block_proximity <- (1 - (min_real_deviation / (base_stability * 1.5))) * 100
        
        # Pruning Logic: We discard branches falling below our critical threshold
        if (block_proximity < critical_threshold) {
            pruned_branches <- pruned_branches + 1
        }
        proximity_history[b] <- block_proximity
        deviation_history[b] <- min_real_deviation
      } else {
        # Automatic pruning occurs if no Diamond data populates the space
        proximity_history[b] <- 0
        deviation_history[b] <- mad_p
        pruned_branches <- pruned_branches + 1
      }
      resonance_history[b] <- fixed_resonance_signature
    }
  }

  # Report Compilation: We structure our final empirical findings
  calc_time <- as.numeric(difftime(Sys.time(), start_time, units = "secs"))
  if(calc_time == 0) calc_time <- 0.000001

  report <- list(
    METRICS_SCALE = c(
      "Total Volume Processed" = N_total, 
      "Vector Memory Size MB" = as.numeric(object.size(raw_input_vector) / (1024^2)), 
      "Pruned Branches (Anom)" = pruned_branches
    ),
    MODAL_VOLUMES = data.frame(
      Absolute_Volume = c(vol_box, vol_diamond, vol_trans, vol_void), 
      Percentage_Share = c(vol_box, vol_diamond, vol_trans, vol_void)/N_total*100, 
      row.names = c("BOX (Matter)", "DIAMOND (Resonance)", "TRANSITION", "VOID (Mutation)")
    ),
    DIAGNOSTICS = c(
      "Target Resonance Signature" = tail(resonance_history, 1), 
      "Average Deviation" = mean(deviation_history[4:n_blocks], na.rm=TRUE), 
      "General Proximity Index %" = mean(proximity_history[4:n_blocks], na.rm=TRUE)
    ),
    PERFORMANCE = c(
      "CPU Calculation Time" = calc_time, 
      "Throughput (rec/sec)" = N_total / calc_time
    )
  )
  class(report) <- "PsiU_Industrial_Report"
  return(report)
}

# S3 Print Method: We output our report in a standardized industrial format
print.PsiU_Industrial_Report <- function(x, ...) {
  sep <- "========================================================================"
  cat("\n", sep, "\n FINAL REPORT - PSI-U MORPHIC AUTOMATON ENGINE \n", sep, "\n\n")
  
  df <- x$MODAL_VOLUMES
  for(i in 1:4) cat(sprintf(" %-22s | Vol: %-8d | Share: %6.3f%%\n", rownames(df)[i], df[i,1], df[i,2]))
  cat("------------------------------------------------------------------------\n")
  cat(sprintf(" General Proximity Index             : %.4f%%\n", x$DIAGNOSTICS[3]))
  cat(sep, "\n")
}
