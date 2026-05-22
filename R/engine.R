#' @title PsiU Engine per Reinforcement Learning
#' @description Interpreta vettori di input come tipi omotopici valutandoli rispetto al Gnomonic Ratio.
#' @param raw_input_vector Un vettore numerico di input.
#' @return Un data.frame con valori, distanze e stati modali.
#' @export
#' @examples
#' # Esempio di utilizzo con valori vicini e lontani dal Gnomonic Ratio
#' inputs <- c(0.618, 0.619, 0.700)
#' PsiU_Engine_RL(inputs)
PsiU_Engine_RL <- function(raw_input_vector) {
  G <- 0.6180339887
  BOX_THRESHOLD <- 0.002
  DIAMOND_THRESHOLD <- 0.010

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
  }

  G_target <- create_hott_type(G, "Gnomonic_Ratio")
  prop_A <- "BOX (Necessity) [\u25a1]"
  prop_B <- "DIAMOND (Possibility) [\u25c6]"

  states <- character(length(raw_input_vector))
  offsets <- numeric(length(raw_input_vector))

  for (i in 1:length(raw_input_vector)) {
    current_u <- create_hott_type(raw_input_vector[i], "Gnomonic_Ratio")
    path_to_G <- create_path(current_u, G_target, tolerance = DIAMOND_THRESHOLD)
    states[i] <- j_rule(path_to_G, prop_A, prop_B)
    offsets[i] <- abs(raw_input_vector[i] - G)
  }

  return(data.frame(Valore_Grezzo = raw_input_vector, Distanza_G = round(offsets, 5), Stato_Modale = states, stringsAsFactors = FALSE))
}

#' @title PsiU MultiLibrary Tree Manager
#' @description Gestisce l'albero di confutazione tableau e la cristallizzazione dei valori.
# Sostituisci le vecchie righe con queste:
prop_A <- " BOX (Necessity) [BOX]"
prop_B <- " DIAMOND (Possibility) [DIAMOND]"

#' @return Una lista contenente la struttura dell'albero aggiornata.
#' @export
#' @examples
#' # Esempio di gestione albero (utilizza un file temporaneo per i test)
#' tmp_file <- tempfile(fileext = ".rds")
#' PsiU_MultiLibrary_Tree(0.618, user_filename = tmp_file)
#' # Pulizia
#' if (file.exists(tmp_file)) unlink(tmp_file)
PsiU_MultiLibrary_Tree <- function(new_value, user_filename = "user_tableau_library.rds") {
  G <- 0.6180339887
  if(file.exists(user_filename)) {
    tree_lib <- readRDS(user_filename)
  } else {
    tree_lib <- list(HISTORY = numeric(), BOX_CRYSTAL = numeric(), NOISE_CRYSTAL = numeric(), STEPS = 0)
  }

  tree_lib$STEPS <- tree_lib$STEPS + 1
  current_res <- PsiU_Engine_RL(new_value)
  str_stato <- current_res$Stato_Modale
  dist_g <- current_res$Distanza_G

  cat(sprintf("[STEP %d] Valore: %.5f | Stato: %s | Distanza G: %.5f\n", tree_lib$STEPS, new_value, str_stato, dist_g))

  if(tree_lib$STEPS <= 3) {
    tree_lib$HISTORY <- c(tree_lib$HISTORY, new_value)
    saveRDS(tree_lib, user_filename)
    return(tree_lib)
  }

  if(str_stato == "DIAMOND (Possibility) [\u25c6]") {
    # Logica Diamond
  } else if(str_stato == "BOX (Necessity) [\u25a1]") {
    tree_lib$BOX_CRYSTAL <- c(tree_lib$BOX_CRYSTAL, new_value)
  } else {
    tree_lib$NOISE_CRYSTAL <- c(tree_lib$NOISE_CRYSTAL, new_value)
  }

  tree_lib$HISTORY <- c(tree_lib$HISTORY, new_value)
  saveRDS(tree_lib, user_filename)
  return(tree_lib)
}

