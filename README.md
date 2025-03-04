# Banzhaf Values for Facts in Query Answering
This repository is the official repository for the paper "Banzhaf Values for Facts in Query Answering"

## Extended version of the paper
Extended version of the paper is available under [Banzhaf_Values_for_Facts_in_Query_Answering.pdf](Banzhaf_Values_for_Facts_in_Query_Answering.pdf)

## Prerequisites

Before you begin, please ensure you have the following installed:

- Python (>=3.9)
- For obtaining provenance expressions of output tuples from queries please refer to https://github.com/navefr/ShapleyForDbFacts

## Algorithms' implementation

Full implementation of the code is in this repository. 
* ExaBan and AdaBan and ItchiBan are available under BanzhafAlgorithms.py
* implementation of adaptations of Monte-Carlo sampling and CNFProxy are available under approximationAlgorithms.py
* Implementation of SIG22 Knowledge compilation algorithm is available under SIG22.py

## Lineages of figure 5 in the article
All the lineages of figure 5 appear in the folder Fig5_Lineages

## Examples
* Example from appendix D showing Banzhaf based ranking and Shapley based ranking don't conicide is [here](notebooks/Banzhaf_and_Shapley_order.ipynb)
