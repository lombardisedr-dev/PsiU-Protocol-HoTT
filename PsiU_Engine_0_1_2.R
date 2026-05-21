
##################################################################
# PSI-U ENGINE OFFICIAL v0.1.2                                   #
# Autore: [Tuo Nome/Idea]                                        #
# Data: 2026-05-21                                               #
# Licenza: Proprietà Intellettuale Riservata                     #
##################################################################

G <- 0.6180339887
BOX_THRESHOLD <- 0.002
DIAMOND_THRESHOLD <- 0.010

PsiU_Engine_0.1.2 <- function(input_vector) {
  offsets <- abs(input_vector - G)
  states <- rep('NOISE (Accident)', length(input_vector))
  states[offsets <= DIAMOND_THRESHOLD] <- 'DIAMOND (Possibility) [◆fgno]'
  states[offsets <= BOX_THRESHOLD]     <- 'BOX (Necessity) [■fgno]'
  
  return(data.frame(
    Valore_Grezzo = input_vector,
    Distanza_G    = round(offsets, 6),
    Stato_Modale  = states,
    Timestamp     = Sys.time(),
    stringsAsFactors = FALSE
  ))
}

PsiU_Library_Manager <- function(results_df, user_filename = 'psiu_library_012.rds') {
  if(file.exists(user_filename)) {
    lib <- readRDS(user_filename)
  } else {
    lib <- list(CRYSTALS = data.frame(), TOTAL_STEPS = 0)
  }
  new_crystals <- results_df[results_df$Stato_Modale != 'NOISE (Accident)', ]
  lib$CRYSTALS <- rbind(lib$CRYSTALS, new_crystals)
  lib$TOTAL_STEPS <- lib$TOTAL_STEPS + nrow(results_df)
  saveRDS(lib, user_filename)
  return(lib)
}

