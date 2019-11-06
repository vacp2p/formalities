# MVDS

TLA+ specification of the [MVDS](https://specs.vac.dev/mvds.html) spec.

## Model Checking

The model uses 2 nodes who both exchange 1 message.

State constraint:

```tla
AllMessagesDelivered
```

The model checker generates 33 distinct states.
