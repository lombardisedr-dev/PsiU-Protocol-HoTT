# ==============================================================================
#           UNIFIED ARCHITECTURE PSI-U: MULTILIBRARY EXCLUSION FILTER
# ==============================================================================

#' @title MultiLibrary Analytical Engine with Exclusion Filter V3
#' @description We evaluate data streams over macro-volumes by segmenting them 
#' into sequential blocks. During the first 3 steps, we accumulate tautologies 
#' and verify their geometric signature. From the 4th step onward, we proceed 
#' by strict exclusion while maintaining a fixed target.
#' @param raw_input_vector Numeric vector containing the raw data stream.
#' @param block_size Numerical size of each temporal block (default = 50000).
#' @return An object of class 'PsiU_Exclusion_Report' ready for the benchmark.
#' @export
PsiU_MultiLibrary_Exclusion_V3 <- function(raw_input_vector, block_size = 50000) {
  
  # 1. GEOMETRIC PARAMETERS AND CONSTANTS OF OUR THEORY
  MATTER_THRESHOLD <- 1/3   # 0.33333... (The first third for matter)
  SPACE_THRESHOLD  <- 2/3   # 0.66667... (The total two thirds of space)
  G_COSMIC         <- SPACE_THRESHOLD * 0.6180339887 # ~0.41202
  DIAMOND_TOLERANCE <- (SPACE_THRESHOLD - MATTER_THRESHOLD) * 0.5 

  N_total  <- length(raw_input_vector)
  n_blocks <- floor(N_total / block_size)
  
  # 2. OUR TAUTOLOGICAL MULTILIBRARY MEMORY STRUCTURES
  MEMORIA_TAUTOLOGICA_P      <- numeric(0)
  MEMORIA_TAUTOLOGICA_GREZZO <- numeric(0)
  
  # We initialize accumulators for temporal block diagnostics
  valori_risonanza_storici <- numeric(n_blocks)
  indici_vicinanza_storici <- numeric(n_blocks)
  scostamenti_medi_storici <- numeric(n_blocks)
  
  # We initialize counters for total modal volumes
  volumi_box <- 0; volumi_diamond <- 0; volumi_transizione <- 0; volumi_vuoto <- 0
  rami_recisi <- 0

  # 3. WE BEGIN THE SEQUENTIAL TEMPORAL BLOCK PROCESSING
  for (b in 1:n_blocks) {
    idx_start <- ((b - 1) * block_size) + 1
    idx_end   <- b * block_size
    block_grezzo <- raw_input_vector[idx_start:idx_end]
    
    # We perform local normalization on the current block (Scale adaptation)
    min_b <- min(block_grezzo)
    max_b <- max(block_grezzo)
    rng_b <- max_b - min_b
    if (rng_b == 0) rng_b <- 1
    val_p <- (block_grezzo - min_b) / rng_b
    
    # We execute vectorized logical operations on the present block
    is_box         <- val_p <= MATTER_THRESHOLD
    is_vuoto       <- val_p > SPACE_THRESHOLD
    in_space       <- !is_box & !is_vuoto
    dist_g         <- abs(val_p - G_COSMIC)
    is_diamond     <- in_space & (dist_g <= DIAMOND_TOLERANCE)
    is_transizione <- in_space & !is_diamond
    
    # We update the macroscopic quantitative historical volumes
    volumi_box         <- volumi_box + sum(is_box)
    volumi_diamond     <- volumi_diamond + sum(is_diamond)
    volumi_transizione <- volumi_transizione + sum(is_transizione)
    volumi_vuoto       <- volumi_vuoto + sum(is_vuoto)
    
    diamond_p      <- val_p[is_diamond]
    diamond_grezzo <- block_grezzo[is_diamond]
    
    # --------------------------------------------------------------------------
    # PHASE 1: FIRST 3 STEPS - WE SAVE TAUTOLOGICAL VALUES (Building the DNA)
    # --------------------------------------------------------------------------
    if (b <= 3) {
      valori_validi_p       <- val_p[is_box | is_diamond]
      valori_validi_grezzi  <- block_grezzo[is_box | is_diamond]
      
      MEMORIA_TAUTOLOGICA_P      <- c(MEMORIA_TAUTOLOGICA_P, valori_validi_p)
      MEMORIA_TAUTOLOGICA_GREZZO <- c(MEMORIA_TAUTOLOGICA_GREZZO, valori_validi_grezzi)
      
      valori_risonanza_storici[b] <- if(length(MEMORIA_TAUTOLOGICA_GREZZO) > 0) mean(MEMORIA_TAUTOLOGICA_GREZZO) else mean(block_grezzo)
      indici_vicinanza_storici[b] <- 71.07  # Our baseline initial control value
      scostamenti_medi_storici[b] <- 0
      
    } else {
      # --------------------------------------------------------------------------
      # PHASE 2: FROM 4TH STEP ONWARD - WE PROCEED BY STRICT EXCLUSION
      # --------------------------------------------------------------------------
      target_proiettato_fisso         <- mean(MEMORIA_TAUTOLOGICA_P)
      VALORE_REALE_DI_RISONANZA_FISSO <- mean(MEMORIA_TAUTOLOGICA_GREZZO)
      
      if (length(diamond_p) > 0) {
        scostamento_medio_p <- mean(abs(diamond_p - target_proiettato_fisso))
        scostamento_grezzo  <- mean(abs(diamond_grezzo - VALORE_REALE_DI_RISONANZA_FISSO))
        
        vicinanza_blocco <- (1 - scostamento_medio_p) * 100
        
        # WE DEFINE THE CRITICAL CRITERION FOR HOMOTOPIC FALLACY
        if (vicinanza_blocco < 71.07) {
          rami_recisi <- rami_recisi + 1
        }
        
        indici_vicinanza_storici[b] <- vicinanza_blocco
        scostamenti_medi_storici[b]  <- scostamento_grezzo
      } else {
        indici_vicinanza_storici[b] <- 100
        scostamenti_medi_storici[b]  <- 0
      }
      valori_risonanza_storici[b] <- VALORE_REALE_DI_RISONANZA_FISSO
    }
  }
  
  # 4. WE COMPILE THE STRUCTURAL COMPONENTS FOR OUR FINAL REPORT
  report <- list(
    SCALA_INPUT = c(
      "Total Volume Analyzed"                    = N_total,
      "Original Tautological Values (Steps 1-3)" = length(MEMORIA_TAUTOLOGICA_P),
      "Severed Branches by Exclusion (Steps 4+)" = rami_recisi
    ),
    VOLUMI_MODALI = data.frame(
      Absolute_Volume   = c(N_total, volumi_box, volumi_diamond, volumi_transizione, volumi_vuoto),
      Percentage_Quota  = c(100.0, (volumi_box/N_total)*100, (volumi_diamond/N_total)*100, (volumi_transizione/N_total)*100, (volumi_vuoto/N_total)*100),
      row.names         = c("Total Stream Volume", "BOX (Matter / Necessity) [\u25a1]", "DIAMOND (Inheritance / Possibility) [\u25c6]", "HOMOTOPIC TRANSITION (Spatial Flow)", "EXPANSIVE VOID (Open Mutation)")
    ),
    DIAGNOSTICA_ESCLUSIONE = c(
      "REAL RESONANCE SIGNATURE (FIXED TARGET)" = tail(valori_risonanza_storici, 1),
      "Mean Deviation from Baseline DNA"        = mean(scostamenti_medi_storici, na.rm=TRUE),
      "Mean Proximity Index of the Process"     = mean(indici_vicinanza_storici, na.rm=TRUE)
    )
  )
  class(report) <- "PsiU_Exclusion_Report"
  return(report)
}

#' @title S3 Print Method for Our PsiU_Exclusion_Report
#' @description We display the structured results by rigidly ordering scale, volumes, and diagnostics.
#' @export
print.PsiU_Exclusion_Report <- function(x, ...) {
  cat("\n========================================================================\n")
  cat("          METRIC BENCHMARK - MULTILIBRARY WITH EXCLUSION FILTER         \n")
  cat("========================================================================\n\n")
  
  cat(" COMPUTATIONAL TREE STRUCTURE\n")
  cat("------------------------------------------------------------------------\n")
  for (i in seq_along(x$SCALA_INPUT)) {
    cat(sprintf("  %-40s : %d\n", names(x$SCALA_INPUT)[i], x$SCALA_INPUT[i]))
  }
  
  cat("\n MAPPING OF TOTAL MODAL VOLUMES\n")
  cat("------------------------------------------------------------------------\n")
  print(round(x$VOLUMI_MODALI, 5))
  
  cat("\n ALIGNMENT DIAGNOSTICS AND EXCLUSION PROCESS\n")
  cat("------------------------------------------------------------------------\n")
  cat(sprintf("  -> %-45s : %.5f\n", names(x$DIAGNOSTICA_ESCLUSIONE), x$DIAGNOSTICA_ESCLUSIONE))
  cat(sprintf("  %-48s : %.5f\n", names(x$DIAGNOSTICA_ESCLUSIONE), x$DIAGNOSTICA_ESCLUSIONE))
  cat(sprintf("  %-48s : %.2f%%\n", names(x$DIAGNOSTICA_ESCLUSIONE), x$DIAGNOSTICA_ESCLUSIONE))
  cat("========================================================================\n")
}
