#' @title PsiU Engine for Cosmic DNA (Modal Version)
#' @description Maps raw input vectors into cosmic spaces based on the 1/3 Matter and 2/3 Space inheritance law.
#' @export
PsiU_Engine_Cosmic_DNA <- function(raw_input_vector) {
  # COSTANTI COSMICHE DELLA VOSTRA TEORIA
  MATTER_THRESHOLD <- 1/3   # 0.33333... (Il primo terzo per la materia)
  SPACE_THRESHOLD <- 2/3    # 0.66667... (I due terzi complessivi di spazio)
  
  # La Sezione Aurea proiettata nello spazio ereditario
  G_COSMIC <- SPACE_THRESHOLD * 0.6180339887 # ~0.41202
  
  # SOGLIE OMOTOPICHE RIGIDE (Derivate dalla geometria 1/3 e 2/3)
  BOX_TOLERANCE <- MATTER_THRESHOLD * 0.1     # Tolleranza di stabilità materiale
  DIAMOND_TOLERANCE <- (SPACE_THRESHOLD - MATTER_THRESHOLD) * 0.5 # Spazio di transizione ereditaria

  # Normalizzazione proiettiva standard 0-1
  if (max(raw_input_vector) > 1 || min(raw_input_vector) < 0) {
    rng <- max(raw_input_vector) - min(raw_input_vector)
    if(rng == 0) rng <- 1
    processed_vector <- (raw_input_vector - min(raw_input_vector)) / rng
  } else {
    processed_vector <- raw_input_vector
  }

  create_hott_type <- function(value, type_label) {
    structure(list(val = value, type = type_label), class = "HoTT_Type")
  }

  states <- character(length(processed_vector))
  offsets <- numeric(length(processed_vector))

  for (i in 1:length(processed_vector)) {
    val_p <- processed_vector[i]
    offsets[i] <- abs(val_p - G_COSMIC)
    
    # LOGICA MODALE EREDITARIA CRISTALLINA
    if (val_p <= MATTER_THRESHOLD) {
      # Il valore è confinato nel terzo della Materia: Geometria Solida
      states[i] <- "BOX (Materia / Necessità) [\u25a1]"
    } else if (val_p > MATTER_THRESHOLD && val_p <= SPACE_THRESHOLD) {
      # Il valore viaggia nel secondo terzo: Spazio di Ereditarietà e Risonanza Gnomonica
      if (abs(val_p - G_COSMIC) <= DIAMOND_TOLERANCE) {
        states[i] <- "DIAMOND (Ereditarietà / Possibilità) [\u25c6]"
      } else {
        states[i] = "TRANSIZIONE OMOTOPICA (Flusso Spaziale)"
      }
    } else {
      # Oltre i 2/3 lo spazio è puro vuoto di espansione non ancora codificato
      states[i] <- "VUOTO ESPANSIVO (Mutazione Aperta)"
    }
  }

  return(data.frame(Valore_Grezzo = raw_input_vector, 
                    Valore_Proiettato = round(processed_vector, 5),
                    Distanza_DNA_Cosmico = round(offsets, 5), 
                    Stato_Modale = states, 
                    stringsAsFactors = FALSE))
}
