# =================================================================
# PROJECT:  PsiU-Protocol
# MODULE:   Standard Engine Ultimate
# VERSION:  1.0.0
# AUTHOR:   ROBERTO LOMBARDI
# DATE:     19/05/2026
# LICENSE:  MIT License
# 
# Copyright (c) 2026 Roberto Lombardi
# 
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
# =================================================================

# --- FORMAL SETUP (G-Limit) ---
# Gnomonic Target (p -> G) - Basato sull'attrattore fondamentale
G <- 0.6180339887  
BOX_THRESHOLD     <- 0.002  # Necessity (□) - Vincolo Stretto
DIAMOND_THRESHOLD <- 0.010  # Possibility (♢) - Vincolo Largo

#' J-Rule Engine Function
#' @description Implementa il trasporto logico dal dato grezzo allo stato modale.
#' @param input_data Vettore numerico di rapporti (ratios).
#' @return Dataframe formale con classificazione modale e risonanza.
psiu_engine <- function(input_data) {
  
  # Calcolo della distanza euclidea dal Limite G
  offset <- abs(input_data - G)
  
  # Mapping Logico-Modale (Trasporto f(tr(A)))
  modal_state <- cut(offset,
                     breaks = c(-Inf, BOX_THRESHOLD, DIAMOND_THRESHOLD, Inf),
                     labels = c("BOX_Necessity (□)", 
                                "DIAMOND_Possibility (♢)", 
                                "VOID_Noise"))
  
  # Indice di Risonanza Percentuale (Confidence Score)
  confidence <- pmax(0, round(100 * (1 - (offset / DIAMOND_THRESHOLD)), 2))
  
  # Costruzione del Quadro Risultante
  results <- data.frame(
    Value     = input_data,
    Offset    = offset,
    State     = modal_state,
    Resonance = paste0(confidence, "%"),
    stringsAsFactors = FALSE
  )
  
  return(results)
}

# --- ESEMPIO DI ESECUZIONE ---
# test_set <- c(0.61803, 0.619, 0.625, 0.450)
# print(psiu_engine(test_set))
