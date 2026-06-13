#' @title PsiU Engine for Reinforcement Learning (Adaptive Version)
#' @description Maps raw input vectors into homotopic spaces by evaluating them against a dynamic, contextual Gnomonic Ratio.
#' @param raw_input_vector A numeric vector representing the incoming data stream.
#' @return A data.frame containing raw values, projected coordinates, G-distances, and modal states.
#' @export
PsiU_Engine_RL_Industrial <- function(raw_input_vector) {
  G <- 0.6180339887
  
  # PROJECTIVE NORMALIZATION: To capture the geometric morphology across different industrial scales
  if (max(raw_input_vector) > 1 || min(raw_input_vector) < 0) {
    rng <- max(raw_input_vector) - min(raw_input_vector)
    if(rng == 0) rng <- 1
    processed_vector <- (raw_input_vector - min(raw_input_vector)) / rng
  } else {
    processed_vector <- raw_input_vector
  }

  # CONTEXTUAL ADAPTIVE THRESHOLDS: Modulating boundaries based on local signal variance
  v_noise <- sd(processed_vector)
  if (is.na(v_noise) || v_noise == 0) v_noise <- 0.01
  
  BOX_THRESHOLD <- v_noise * 0.1     
  DIAMOND_THRESHOLD <- v_noise * 0.5 

  create_hott_type <- function(value, type_label) {
    structure(list(val = value, type = type_label), class = "HoTT_Type")
  }

  create_path <- function(type_a, type_b, tolerance) {
    if (type_a$type != type_b$type) return(NULL)
    distance <- abs(type_a$val - type_b$val)
    if (distance <= tolerance) return(list(from = type_a, to = type_b, distance = distance, proof = "Reflexivity_Path"))
    else return(NULL)
  }

  j_rule <- function(path, property_A, property_B) {
    if (is.null(path)) return("NOISE (Accident)")
    if (path$distance <= BOX_THRESHOLD) return(property_A)
    if (path$distance <= DIAMOND_THRESHOLD) return(property_B)
    return("NOISE (Accident)")
  }

  G_target <- create_hott_type(G, "Gnomonic_Ratio")
  prop_A <- "BOX (Necessity) [\u25a1]"
  prop_B <- "DIAMOND (Possibility) [\u25c6]"

  states <- character(length(processed_vector))
  offsets <- numeric(length(processed_vector))

  for (i in 1:length(processed_vector)) {
    current_u <- create_hott_type(processed_vector[i], "Gnomonic_Ratio")
    path_to_G <- create_path(current_u, G_target, tolerance = DIAMOND_THRESHOLD)
    states[i] <- j_rule(path_to_G, prop_A, prop_B)
    offsets[i] <- abs(processed_vector[i] - G)
  }

  return(data.frame(Valore_Grezzo = raw_input_vector, 
                    Valore_Proiettato = round(processed_vector, 5),
                    Distanza_G = round(offsets, 5), 
                    Stato_Modale = states, 
                    stringsAsFactors = FALSE))
}

#' @title PsiU MultiLibrary Tree Manager with Resonant Cross-Validation
#' @description Evaluates ongoing structural resonance between the incoming data point and the verified historical data library.
#' @param new_value A single numeric value to be evaluated and classified within the tableau tree.
#' @param user_filename A character string specifying the RDS file location. If NULL, a temporary path is used.
#' @param verbose Logical. If TRUE, outputs the structural resonance report directly to the console.
#' @return A list containing the updated library structure and the latest resonance assessment.
#' @export
PsiU_MultiLibrary_Tree_Resonant <- function(new_value, user_filename = NULL, verbose = TRUE) {
  G <- 0.6180339887
  
  if (is.null(user_filename)) {
    user_filename <- file.path(tempdir(), "user_tableau_library_resonant.rds")
  }

  if(file.exists(user_filename)) {
    tree_lib <- readRDS(user_filename)
  } else {
    tree_lib <- list(HISTORY = numeric(), 
                     BOX_CRYSTAL = numeric(), 
                     DIAMOND_RESERVE = numeric(), 
                     NOISE_CRYSTAL = numeric(), 
                     STEPS = 0)
  }

  tree_lib$STEPS <- tree_lib$STEPS + 1
  tree_lib$HISTORY <- c(tree_lib$HISTORY, new_value)
  
  # Evaluating via adaptive HoTT engine
  current_res <- PsiU_Engine_RL_Industrial(tree_lib$HISTORY)
  str_stato <- tail(current_res$Stato_Modale, 1)
  dist_g <- tail(current_res$Distanza_G, 1)
  val_proiettato <- tail(current_res$Valore_Proiettato, 1)

  # Dynamic modal routing (the rigid 3-step block has been completely removed)
  if(str_stato == "DIAMOND (Possibility) [\u25c6]") {
    tree_lib$DIAMOND_RESERVE <- c(tree_lib$DIAMOND_RESERVE, new_value)
    diagnostica <- "DIFFICOLTÀ DI CHIUSURA: Il valore fluttua nella possibilità temporanea."
  } else if(str_stato == "BOX (Necessity) [\u25a1]") {
    tree_lib$BOX_CRYSTAL <- c(tree_lib$BOX_CRYSTAL, new_value)
    diagnostica <- "CRISTALLIZZAZIONE: Il valore ha trovato stabilità formale nel DNA computazionale."
  } else {
    tree_lib$NOISE_CRYSTAL <- c(tree_lib$NOISE_CRYSTAL, new_value)
    diagnostica <- "STASI GNOMONICA: Struttura fallace recisa per deviazione geometrica eccessiva."
  }

  # --- TRANS-DIMENSIONAL RESONANCE COMPILER ---
  report_risonanza <- "Inizializzazione libreria (Nessun cristallo precedente con cui risuonare)"
  qualita_risonanza <- "Incompleta"
  
  if (length(tree_lib$BOX_CRYSTAL) > 0) {
    esiti_motore <- PsiU_Engine_RL_Industrial(tree_lib$BOX_CRYSTAL)
    media_cristalli_proiettati <- mean(esiti_motore$Valore_Proiettato)
    
    discrepanza_locale <- abs(val_proiettato - media_cristalli_proiettati)
    
    if (discrepanza_locale <= 0.005) {
      qualita_risonanza <- "ASSONANZA PURA [\u266b]"
      report_risonanza <- sprintf("Il valore risuona perfettamente con la memoria reale della libreria (Discrepanza: %.5f). Configurazione validata trans-dimensionalmente.", discrepanza_locale)
    } else if (discrepanza_locale <= 0.025) {
      qualita_risonanza <- "ASSONANZA PARZIALE / MITIGATA"
      report_risonanza <- sprintf("Rilevata assonanza parziale con scostamento tollerabile (Discrepanza: %.5f). La coerenza di Reedy è preservata tramite approssimazione omotopica.", discrepanza_locale)
    } else {
      qualita_risonanza <- "DISSONANZA STRUTTURALE (Rumore)"
      report_risonanza <- sprintf("Forte discrepanza rispetto ai risultati reali stabili (Discrepanza: %.5f). Il sistema rileva una fallacia di matching.", discrepanza_locale)
    }
  }

  if (verbose) {
    cat(sprintf("\n--- [REPORT DI RISONANZA STEP %d] ---\n", tree_lib$STEPS))
    cat(sprintf("Valore Grezzo: %.5f | Valore Proiettato: %.5f\n", new_value, val_proiettato))
    cat(sprintf("Stato Modale:  %s\n", str_stato))
    cat(sprintf("Esito Rete:    %s\n", qualita_risonanza))
    cat(sprintf("Dettaglio:     %s\n", report_risonanza))
    cat(sprintf("Diagnostica:   %s\n", diagnostica))
    cat("--------------------------------------------\n")
  }

  saveRDS(tree_lib, user_filename)
  
  return(list(Library = tree_lib, 
              Current_Report = list(Stato = str_stato, 
                                    Risonanza = qualita_risonanza, 
                                    Dettaglio = report_risonanza)))
}
