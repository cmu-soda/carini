# Carini

Carini (Compositionally Arranged INductive Invariants) is a tool that helps with *fully compositional* inductive invariant inference for formal specifications written in TLA+.
More specifically, Carini accepts as input two components $C_1$ and $C_2$ and a safety property $P$ with the goal of proving that $C_1 \parallel C_2 \models P$.
Carini attempts compsitional verification, i.e. it tries to find an *assumption* $A$ such that $\langle A \rangle C_1 \langle P \rangle$ and $\langle \text{True} \rangle C_2 \langle A \rangle$.
The notation $\langle \alpha \rangle C \langle \gamma \rangle$ indicates an *assume-guarantee contract*, meaning that the component $C$ guarantees $\gamma$ under the assumption $\alpha$.

If Carini succeeds, it will output a "_hist" TLA+ specification for each component, which represents the contract for each component.
Then, any off-the-shelf invariant inference tool can be used to find a *local inductive invariant* for the two _hist specifications.
For example, one can use the [Endive](https://github.com/will62794/endive) tool for local invariant inference.
By construction, the conjunction of the two local invariants is an inductive invariant that proves $C_1 \parallel C_2 \models P$.


## Usage
We are currently working on adding instructions for how to use this tool.
We will have the instructions ready by September 30th 2025.
