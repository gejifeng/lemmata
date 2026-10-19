"""lean_prover: a small, Lean-arbitrated theorem-proving agent.

The only hard gates are: statement unchanged (by construction), no sorry,
and `#print axioms` showing only the standard axioms.
"""

from . import dotenv as _dotenv

# Settings (model endpoint, API key, concurrency, paths) can live in a `.env` file at the project root;
# see `.env.example`. Real environment variables take precedence.
_dotenv.load()
