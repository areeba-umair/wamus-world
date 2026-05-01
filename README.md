Wumpus World is a classic Artificial Intelligence project built with Python and Flask. It simulates a grid-based environment where a Knowledge-Based Agent must navigate safely while avoiding hidden pits and a dangerous Wumpus monster.

The agent cannot see the grid directly. Instead it relies on two percepts — BREEZE which means a pit is nearby, and STENCH which means the Wumpus is nearby. Using these clues, the agent builds a Knowledge Base and applies propositional logic with resolution inference to reason about which cells are safe before moving into them.

Key features of the project:

- Knowledge Base stores all facts as CNF clauses
- TELL adds new observations to the KB after each move
- ASK queries the KB using resolution refutation to prove cell safety
- Agent always prefers proven safe cells over unknown risk cells
- Scoring system rewards exploration and penalizes death
- Configurable grid size and number of pits
- Web-based interface built with Flask, HTML, CSS and JavaScript
