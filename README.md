# PrototypeWithInterface
All interesting content is found in the src directory
- src/robot contains the "Robot" (Haskell) code  - the actual mathematical content lies here
- src/APICode contains Haskell code which controls how the server works. The server right now acts as a simple API which accepts POST requests to perform moves in a web interface
- src/static contains HTML/CSS/JS controlling how the front-end webapp works. This webapp makes POST requests to the server to make moves.
- src/Lib.hs is the beating heart of the server and is where the code runs for the server is actually called and runs

## To-do
- Fix library equivalence move to allow conditions to lie below the expression being changed.
- Implement backwards library reasoning with nested boxes.
- Implement quality of life "tidyEverything" move with nested boxes.

- Think about/start implementing a type system (I'm increasingly thinking it is necessary).
- Think about library search and implement a simple system.
- Think about how the interface will work with library search and start implementing.

- Write some basic template code to choose moves automatically and start playing with move scoring.
